pragma solidity ^0.4.0;

/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {

    /**
    * @dev Multiplies two numbers, throws on overflow.
    */
    function mul(uint256 a, uint256 b) internal pure returns (uint256 c) {
        if (a == 0) {
            return 0;
        }
        c = a * b;
        assert(c / a == b);
        return c;
    }

    /**
    * @dev Integer division of two numbers, truncating the quotient.
    */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // assert(b > 0); // Solidity automatically throws when dividing by 0
        // uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold
        return a / b;
    }

    /**
    * @dev Subtracts two numbers, throws on overflow (i.e. if subtrahend is greater than minuend).
    */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        assert(b <= a);
        return a - b;
    }

    /**
    * @dev Adds two numbers, throws on overflow.
    */
    function add(uint256 a, uint256 b) internal pure returns (uint256 c) {
        c = a + b;
        assert(c >= a);
        return c;
    }
}

library Set {
    // We define a new struct datatype that will be used to
    // hold its data in the calling contract.
    struct Data {
             mapping(address => bool) flags;
             address[] values;
         }

/*
    A Contract Contract for order processing in CPChain.
    Note: This is experimental, don't use it in main-net for now.
*/
contract Contract {

    using SafeMath for uint256;

    enum State {
        Created,
        SellerConfirmed,
        ProxyFetched,
        ProxyDelivered,
        BuyerConfirmed,
        Finished,
        SellerRated,
        BuyerRated,
        Disputed,
        Withdrawn
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

    enum DisputeState {
        Proposed,
        Processed,
        Handled
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
    uint DisputeTimeAllowed = 100;

    address public trentAddress;

    uint public numOrders = 0;
    uint public numDisputes = 0;
    // TODO let records to be public or only let relevant address to be a accessible
    mapping(uint => OrderInfo) public orderRecords;
    mapping(uint => DisputeInfo) public disputeRecords;

    mapping(address => uint) public proxyCredits;
    
    mapping(address => uint) public proxyDeposits;

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
    
    modifier onlyTrent() {require(msg.sender == trentAddress); _;}

    function Contract() public {
        trentAddress = msg.sender;
    }

    function() payable {
    }

    // Some events that help tracking the status of the chain
    event OrderInitiated(address from, uint orderId, uint value);
    event OrderWithdrawn(uint orderId);

    event SellerConfirmed(uint orderId, uint value);

    event ProxyFetched(uint orderId);
    event ProxyDelivered(uint orderId);

    event BuyerConfirmed(uint orderId);
    event BuyerDisputed(uint orderId);

    event SellerClaimTimeout(uint orderId);

    event OrderFinished(uint orderId);

    event ProxyDeposited(address from, uint value);
    event ProxyWithdrawn(address from, uint value);

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
        emit OrderInitiated(msg.sender, numOrders, msg.value);
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
        emit OrderWithdrawn(id);
    }

    function buyerClaimTimeOut(uint id)
        public
        onlyBuyer(id)
        inState(id, State.Created)
        onlyAfter(orderRecords[id].endTime)
    {
        orderRecords[id].state = State.Withdrawn;
        orderRecords[id].buyerAddress.transfer(orderRecords[id].offeredPrice);
        emit OrderWithdrawn(id);
    }


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

        uint paySeller = orderRecords[id].offeredPrice.sub(payProxy.mul(2));
        orderRecords[id].sellerAddress.transfer(paySeller);
        orderRecords[id].state = State.Finished;

        emit BuyerConfirmed(id);
    }

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
        emit BuyerDisputed(id);

    }

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
            emit OrderFinished(id);
        }

    }

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

        orderRecords[id].state = State.BuyerRated;

    }

    function sellerConfirm(uint id)
        public
        onlySeller(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.Created)
        payable
    {
        require(msg.value == orderRecords[id].offeredPrice);
        orderRecords[id].state = State.SellerConfirmed;

        emit SellerConfirmed(id, msg.value);
    }

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
            emit OrderFinished(id);
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

        emit SellerClaimTimeout(id);
    }

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

        orderRecords[id].state = State.SellerRated;

    }

    function proxyDeposit()
        public
        payable
    {
        require(msg.value > 0);
        proxyDeposits[msg.sender] = proxyDeposits[msg.sender].add(msg.value);

        emit ProxyDeposited(msg.sender, msg.value);
    }

    function proxyWithdraw(uint value)
        public
    {
        require(value > 0 && value <= proxyDeposits[msg.sender]);
        proxyDeposits[msg.sender] = proxyDeposits[msg.sender].sub(value);
        (msg.sender).transfer(value);

        emit ProxyWithdrawn(msg.sender, value);
    }

    function proxyFetched(uint id)
        public
        onlyProxy(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.SellerConfirmed)
    {
        orderRecords[id].state = State.ProxyFetched;

        emit ProxyFetched(id);
    }

    function proxyDelivered(bytes32 deliverHash, uint id)
        public
        onlyProxy(id)
        onlyBefore(orderRecords[id].endTime)
        inState(id, State.ProxyFetched)
    {
        orderRecords[id].state = State.ProxyDelivered;
        orderRecords[id].deliverHash = deliverHash;

        emit ProxyDelivered(id);
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
        onlyTrent()
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
                trentAddress.transfer(proxyFee.mul(2));
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

                trentAddress.transfer(offeredPrice.div(2).add(proxyFee.mul(2)));
            }
            else {
                proxyAddress.transfer(proxyFee);
                secondaryProxyAddress.transfer(proxyFee);

                trentAddress.transfer(offeredPrice.div(2).sub(proxyFee.mul(2)));
            }
        }
        emit OrderFinished(orderId);
    }

}
