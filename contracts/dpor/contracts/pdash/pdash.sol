pragma solidity ^0.4.0;

/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
import "../../lib/safeMath.sol";


/*
    A Contract Contract for order processing in CPChain.
    Note: This is experimental, don't use it in main-net for now.
*/
contract Pdash {

    using SafeMath for uint256;
    // transaction status
    enum State {
        Created,
        SellerConfirmed,
        ProxyFetched,
        ProxyDelivered,
        BuyerConfirmed,
        Finished,
        SellerRated,
        BuyerRated,
        AllRated,
        Disputed,
        Withdrawn
    }
    // dispute status
    enum DisputeState {
        Proposed,
        Processed,
        Handled
    }

    struct OrderInfo {
        bytes32 descHash;
        bytes buyerRSAPubkey;
        address buyerAddress;
        address sellerAddress;
        address proxyAddress;
        address secondaryProxyAddress;
        uint offeredPrice;
        uint proxyFee;
        bytes32 deliverHash;
        uint endTime;
        State state;
        uint disputeId;
    }
    struct DisputeInfo {
        uint orderId;
        bool badBuyer;
        bool badSeller;
        bool badProxy;
        bool buyerAgree;
        bool sellerAgree;
        uint endTime;
        DisputeState disputeState;
    }

    address public owner;
    uint DisputeTimeAllowed = 100;
    uint public numOrders = 0;
    uint public numDisputes = 0;
    // TODO let records to be public or only let relevant address to be a accessible
    mapping(uint => OrderInfo) public orderRecords;
    mapping(uint => DisputeInfo) public disputeRecords;
    mapping(address => uint) public proxyCredits;
    mapping(address => uint) public proxyDeposits;
    // the orders id in a certain block.
    mapping(uint => uint[]) public blockOrders;
    // the number of orders in a certain block.
    mapping(uint => uint) public blockOrdersLength;

    // Security Checks
    modifier onlyBefore(uint time) {require(now < time); _;}
    modifier onlyAfter(uint time) {require(now > time); _;}
    modifier onlyBuyer(uint id) {require(msg.sender == orderRecords[id].buyerAddress); _;}
    modifier onlySeller(uint id) {require(msg.sender == orderRecords[id].sellerAddress); _;}
    modifier onlyProxy(uint id) {
        require(
            msg.sender == orderRecords[id].proxyAddress ||
            msg.sender == orderRecords[id].secondaryProxyAddress
        );
        _;
    }
    modifier inState(uint id, State _state) {require(orderRecords[id].state == _state); _;}
    modifier inDisputeState(uint id, DisputeState _state) {require(disputeRecords[id].disputeState == _state); _;}
    modifier onlyOwner() {require(msg.sender == owner); _;}

    constructor() public {
        owner = msg.sender;
    }

    function() public payable { }

    // Some events that help tracking the status of the orders.
    event OrderInitiated(address from, uint orderId, uint value, uint time);
    event OrderWithdrawn(uint orderId, uint time);
    event SellerConfirmed(uint orderId, uint value, uint time);
    event ProxyFetched(uint orderId, uint time);
    event ProxyDelivered(uint orderId, uint time);
    event BuyerConfirmed(uint orderId, uint time);
    event BuyerDisputed(uint orderId, uint time);
    event SellerClaimTimeout(uint orderId, uint time);
    event OrderFinished(uint orderId, uint time);
    event ProxyDeposited(address from, uint value, uint time);
    event ProxyWithdrawn(address from, uint value, uint time);

    function placeOrder(
        bytes32 descHash,
        bytes buyerRSAPubkey,
        address seller,
        address proxy,
        address secondaryProxy,
        uint proxyFee,
        uint timeAllowed
    )
        public
        payable
    {
        require(msg.value > proxyFee.mul(2));
        numOrders = numOrders.add(1);
        orderRecords[numOrders] = OrderInfo({
            descHash: descHash,
            buyerRSAPubkey: buyerRSAPubkey,
            buyerAddress: msg.sender,
            sellerAddress: seller,
            proxyAddress: proxy,
            secondaryProxyAddress: secondaryProxy,
            deliverHash: bytes32(0),
            offeredPrice: msg.value,
            proxyFee: proxyFee,
            endTime: now.add(timeAllowed),
            state: State.Created,
            disputeId: 0
        });
        blockOrders[block.number].push(numOrders);
        blockOrdersLength[block.number].add(1);
        emit OrderInitiated(msg.sender, numOrders, msg.value, now);
    }

    function buyerWithdraw(uint id)
        public
        onlyBuyer(id)
        onlyBefore(orderRecords[id].endTime)
    {
        if (orderRecords[id].state == State.Created)
        {
            orderRecords[id].state = State.Withdrawn;
            orderRecords[id].buyerAddress.transfer(orderRecords[id].offeredPrice);
        }
        else if (orderRecords[id].state == State.SellerConfirmed)
        {
            orderRecords[id].state = State.Withdrawn;
            orderRecords[id].buyerAddress.transfer(orderRecords[id].offeredPrice);
            orderRecords[id].sellerAddress.transfer(orderRecords[id].offeredPrice);
        }
        emit OrderWithdrawn(id, now);
    }

    function buyerClaimTimeOut(uint id)
        public
        onlyBuyer(id)
        inState(id, State.Created)
        onlyAfter(orderRecords[id].endTime)
    {
        orderRecords[id].state = State.Withdrawn;
        orderRecords[id].buyerAddress.transfer(orderRecords[id].offeredPrice);
        emit OrderWithdrawn(id, now);
    }

    // buyer confirm tx
    function buyerConfirmDeliver(uint id)
        public
        onlyBuyer(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.ProxyDelivered)
    {
        orderRecords[id].state = State.BuyerConfirmed;

        uint payProxy = orderRecords[id].proxyFee;
        orderRecords[id].proxyAddress.transfer(payProxy);
        orderRecords[id].secondaryProxyAddress.transfer(payProxy);
        // exchange the calc step to save gas.
        uint paySeller = (orderRecords[id].offeredPrice.sub(payProxy)).mul(2);
        orderRecords[id].sellerAddress.transfer(paySeller);
        orderRecords[id].state = State.Finished;

        emit BuyerConfirmed(id, now);
    }

    // buyer dispute tx
    function buyerDispute(uint id)
        public
        onlyBuyer(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.ProxyDelivered)
    {
        orderRecords[id].state = State.Disputed;
        numDisputes = numDisputes.add(1);
        orderRecords[id].disputeId = numDisputes;
        disputeRecords[numDisputes] = DisputeInfo({
            orderId: id,
            badBuyer: false,
            badSeller: false,
            badProxy: false,
            buyerAgree: false,
            sellerAgree: false,
            endTime: now.add(DisputeTimeAllowed),
            disputeState: DisputeState.Proposed
        });
        emit BuyerDisputed(id, now);

    }
    // buyer agreee or not the tx
    function buyerAgreeOrNot(uint id, bool if_agree)
        public
        onlyBuyer(id)
        inState(id, State.Disputed)
        onlyBefore(disputeRecords[orderRecords[id].disputeId].endTime)
        inDisputeState(orderRecords[id].disputeId, DisputeState.Processed)
    {
        uint disputeId = orderRecords[id].disputeId;
        disputeRecords[disputeId].buyerAgree = if_agree;
        if (disputeRecords[disputeId].buyerAgree && disputeRecords[disputeId].sellerAgree)
        {
            // handle dispute
            finishDispute(id, disputeId, disputeRecords[disputeId].badBuyer, disputeRecords[disputeId].badSeller, disputeRecords[disputeId].badProxy);
            emit OrderFinished(id, now);
        }
    }
    // buyer give a Score to buyer
    function buyerRateProxy(uint id, uint rate)
        public
        onlyBuyer(id)
    {
        require(orderRecords[id].state == State.Finished || orderRecords[id].state == State.SellerRated);
        require(rate > 0 && rate < 10);
        proxyCredits[orderRecords[id].proxyAddress] = proxyCredits[orderRecords[id].proxyAddress].add(rate);
        proxyCredits[orderRecords[id].proxyAddress] = proxyCredits[orderRecords[id].proxyAddress].div(2);

        proxyCredits[orderRecords[id].secondaryProxyAddress] = proxyCredits[orderRecords[id].secondaryProxyAddress].add(rate);
        proxyCredits[orderRecords[id].secondaryProxyAddress] = proxyCredits[orderRecords[id].secondaryProxyAddress].div(2);
        if(orderRecords[id].state == State.Finished){
            orderRecords[id].state = State.BuyerRated;
        }else{
            orderRecords[id].state = State.AllRated;
        }
    }
    // seller confirm the order
    function sellerConfirm(uint id)
        public
        onlySeller(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.Created)
        payable
    {
        require(msg.value == orderRecords[id].offeredPrice);
        orderRecords[id].state = State.SellerConfirmed;

        emit SellerConfirmed(id, msg.value, now);
    }

    // seller agree oe not to the proxy
    function sellerAgreeOrNot(uint id, bool if_agree)
        public
        onlySeller(id)
        inState(id, State.Disputed)
        onlyBefore(disputeRecords[orderRecords[id].disputeId].endTime)
        inDisputeState(orderRecords[id].disputeId, DisputeState.Processed)
    {
        uint disputeId = orderRecords[id].disputeId;
        disputeRecords[disputeId].sellerAgree = if_agree;
        if (disputeRecords[disputeId].buyerAgree && disputeRecords[disputeId].sellerAgree)
        {
            // handle dispute.
            finishDispute(id, disputeId, disputeRecords[disputeId].badBuyer, disputeRecords[disputeId].badSeller,disputeRecords[disputeId].badProxy);
            emit OrderFinished(id, now);
        }

    }

    function sellerClaimTimeOut(uint id)
        public
        onlySeller(id)
        inState(id, State.ProxyDelivered)
        onlyAfter(orderRecords[id].endTime)
    {
        orderRecords[id].state = State.Finished;

        uint payProxy = orderRecords[id].proxyFee;
        orderRecords[id].proxyAddress.transfer(payProxy);
        orderRecords[id].secondaryProxyAddress.transfer(payProxy);

        orderRecords[id].sellerAddress.transfer(orderRecords[id].offeredPrice); // pay back seller's deposit.

        uint paySeller = orderRecords[id].offeredPrice.sub(payProxy.mul(2));
        orderRecords[id].sellerAddress.transfer(paySeller); // pay seller.

        emit SellerClaimTimeout(id, now);
    }

    // seller score to proxy
    function sellerRateProxy(uint id, uint rate)
        public
        onlySeller(id)
    {
        require(orderRecords[id].state == State.Finished || orderRecords[id].state == State.BuyerRated);
        require(rate > 0 && rate < 10);
        proxyCredits[orderRecords[id].proxyAddress] = proxyCredits[orderRecords[id].proxyAddress].add(rate);
        proxyCredits[orderRecords[id].proxyAddress] = proxyCredits[orderRecords[id].proxyAddress].div(2);

        proxyCredits[orderRecords[id].secondaryProxyAddress] = proxyCredits[orderRecords[id].secondaryProxyAddress].add(rate);
        proxyCredits[orderRecords[id].secondaryProxyAddress] = proxyCredits[orderRecords[id].secondaryProxyAddress].div(2);
        if(orderRecords[id].state == State.Finished){
            orderRecords[id].state = State.SellerRated;
        }else{
            orderRecords[id].state = State.AllRated;
        }

    }

    // proxy deposit
    function proxyDeposit()
        public
        payable
    {
        require(msg.value > 0);
        proxyDeposits[msg.sender] = proxyDeposits[msg.sender].add(msg.value);

        emit ProxyDeposited(msg.sender, msg.value, now);
    }

    function proxyWithdraw(uint value)
        public
    {
        require(value > 0 && value <= proxyDeposits[msg.sender]);
        proxyDeposits[msg.sender] = proxyDeposits[msg.sender].sub(value);
        (msg.sender).transfer(value);

        emit ProxyWithdrawn(msg.sender, value, now);
    }

    // proxy git the data
    function proxyFetched(uint id)
        public
        onlyProxy(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.SellerConfirmed)
    {
        orderRecords[id].state = State.ProxyFetched;

        emit ProxyFetched(id, now);
    }

    // proxy give buyer the data address
    function proxyDelivered(bytes32 deliverHash, uint id)
        public
        onlyProxy(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.ProxyFetched)
    {
        orderRecords[id].state = State.ProxyDelivered;
        orderRecords[id].deliverHash = deliverHash;

        emit ProxyDelivered(id, now);
    }

    function proxyProcessDispute(uint id, bool decision)
        public
        onlyProxy(id)
        onlyBefore(disputeRecords[orderRecords[id].disputeId].endTime)
        inState(id, State.Disputed)
    {
        uint disputeId = orderRecords[id].disputeId;
        disputeRecords[disputeId].disputeState = DisputeState.Processed;
        if (decision)
        {
            disputeRecords[disputeId].badBuyer = false;
            disputeRecords[disputeId].badSeller = true;
        }
        else {
            disputeRecords[disputeId].badBuyer = true;
            disputeRecords[disputeId].badSeller = false;
        }
    }

    function trentHandleDispute(uint id, bool badBuyer, bool badSeller, bool badProxy)
        public
        onlyOwner
        inState(id, State.Disputed)
    {
        uint orderId = id;
        uint disputeId = orderRecords[orderId].disputeId;

        require(disputeRecords[disputeId].disputeState == DisputeState.Processed);
//        require(badBuyer && badSeller && badProxy == false);
//        require((badBuyer && !badSeller) || (!badBuyer && badSeller));
//        require(disputeRecords[disputeId].endTime < now);
        disputeRecords[disputeId].badBuyer = badBuyer;
        disputeRecords[disputeId].badSeller = badSeller;
        disputeRecords[disputeId].badProxy = badProxy;

        finishDispute(orderId, disputeId, badBuyer, badSeller, badProxy);

    }

    function finishDispute(uint orderId, uint disputeId, bool badBuyer, bool badSeller, bool badProxy)
        private
    {
        orderRecords[orderId].state = State.Finished;
        disputeRecords[disputeId].disputeState = DisputeState.Handled;
        address buyerAddress = orderRecords[orderId].buyerAddress;
        address sellerAddress = orderRecords[orderId].sellerAddress;
        address proxyAddress = orderRecords[orderId].proxyAddress;
        address secondaryProxyAddress = orderRecords[orderId].secondaryProxyAddress;
        uint offeredPrice = orderRecords[orderId].offeredPrice;
        uint proxyFee = orderRecords[orderId].proxyFee;

        if (badBuyer)
        {
            sellerAddress.transfer(offeredPrice.add(offeredPrice.sub(proxyFee.mul(2)))); // pay back seller's deposit.
            if (badProxy)
            {
                proxyDeposits[proxyAddress].sub(proxyFee); // punish bad proxy.
                proxyDeposits[secondaryProxyAddress].sub(proxyFee);

                sellerAddress.transfer(proxyFee.mul(2));
                owner.transfer(proxyFee.mul(2));
            }
            else {
                proxyAddress.transfer(proxyFee);
                secondaryProxyAddress.transfer(proxyFee);
            }
        }
        else if (badSeller)
        {
            buyerAddress.transfer(offeredPrice);
            sellerAddress.transfer(offeredPrice.div(2));
            if (badProxy)
            {
                proxyDeposits[proxyAddress].sub(proxyFee); // punish bad proxy.
                proxyDeposits[secondaryProxyAddress].sub(proxyFee);

                owner.transfer(offeredPrice.div(2).add(proxyFee.mul(2)));
            }
            else {
                proxyAddress.transfer(proxyFee);
                secondaryProxyAddress.transfer(proxyFee);

                owner.transfer(offeredPrice.div(2).sub(proxyFee.mul(2)));
            }
        }
        emit OrderFinished(orderId, now);
    }

}
