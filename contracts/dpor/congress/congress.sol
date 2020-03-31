/**
 * congress contract is for nodes to join and quit congress
**/

pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Congress {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner; // owner has permissions to modify parameters
    uint256 public period = 90 days; // members can withdraw deposit after period, owner can change period
    uint256 public congressThreshold = 200000 ether; // standard to join congress, minimal amount, owner can change
    uint256 public supportedVersion = 1; // version control
    Set.Data private members; // members group
    // enabled indicates status of contract, only when it is true, nodes can join congress.
    bool public enabled = true;

    struct Participant {
        uint256 lockedDeposit;
        uint256 lockedTime;
    }

    // store a 'Participant' struct for each possible address
    mapping (address => Participant) public Participants;

    // new members join, Join will be emitted, containing 'who' locked 'how much' money at 'when'
    // members quit, Quit will be emitted
    event Join(address who, uint256 lockedDeposit, uint256 lockedTime);
    event Quit(address who);
    event ownerRefund(address who, uint256 amount);
    event ownerRefundAll(uint256 numOfInvestor);

    // the '_' in modifier will be replaced by code in function;
    // if there are more than one modifiers in a function, '_' in first modifier will be replaced by code in second modifier
    // cf. https://ethereum.stackexchange.com/questions/29608/whats-the-order-of-execution-for-multiple-function-modifiers?rq=1
    modifier onlyOwner() {require(msg.sender == owner);_;}
    modifier onlyEnabled() {require(enabled);_;}

    constructor () public {
        owner = msg.sender;
    }

    // there are there requirements for join congress:
    // 1. contract address can not join;
    // 2. members those alreay in congress can not deposit again;
    // 3. deposit money has to satisfy threshold.
    function joinCongress(uint256 version) public payable onlyEnabled {
        require(version >= supportedVersion);
        require(!isContract(msg.sender),"please not use contract call this function");
        require(!members.contains(msg.sender));
        require(msg.value >= congressThreshold);

        // if requirements above are satisfied, the node will be added into congress
        // lockedDeposit and lockedTime will be recorded in 'Participants'
        Participants[msg.sender].lockedDeposit = Participants[msg.sender].lockedDeposit.add(msg.value);
        Participants[msg.sender].lockedTime = block.timestamp;

        // the node will be inserted into members group
        members.insert(msg.sender);

        emit Join(msg.sender, Participants[msg.sender].lockedDeposit, Participants[msg.sender].lockedTime);
    }

    // a node can join congress anytime on conditions that:
    // 1. the node has to be in membets group;
    // 2. the node must quit after at least a period.
    function quitCongress() public {
        require(members.contains(msg.sender));
        require(Participants[msg.sender].lockedTime + period <= block.timestamp);

        // if requirements above are satisfied, the node will receive locked deposit
        msg.sender.transfer(Participants[msg.sender].lockedDeposit);
        Participants[msg.sender].lockedDeposit = 0;

        // the node will be removed from congress group
        members.remove(msg.sender);

        emit Quit(msg.sender);
    }

    // owner refunds one investor
    function refund(address investor) public onlyOwner {
        require(members.contains(investor));
        uint256 amount = Participants[investor].lockedDeposit;
        investor.transfer(amount);
        Participants[investor].lockedDeposit = 0;
        members.remove(investor);

        emit ownerRefund(investor, amount);
    }

    // owner refunds all investors
    function refundAll() public onlyOwner {
        uint256 num = members.values.length;
        for(uint i=0; i<num; i++){
            address investor = members.values[0];
            uint256 deposit = Participants[investor].lockedDeposit;
            investor.transfer(deposit);
            Participants[investor].lockedDeposit = 0;
            members.remove(investor);

            emit ownerRefund(investor, deposit);
        }
        assert(members.values.length == 0);

        emit ownerRefundAll(num);
    }

    // owner can enable and disable congress contract
    function enableContract() public onlyOwner {
        enabled = true;
    }

    function disableContract() public onlyOwner {
        enabled = false;
    }

    // owner can set period, threshold and supported version
    function setPeriod(uint256 _period) public onlyOwner {
        require(_period <= 1 days);
        period = _period;
    }

    function setCongressThreshold(uint256 threshold) public onlyOwner {
        require(threshold >= 200000 ether);
        congressThreshold = threshold;
    }

    function setSupportedVersion(uint256 version) public onlyOwner {
        supportedVersion = version;
    }

    // judge if an address is a contract address
    function isContract(address addr) public view returns (bool) {
        uint size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    // check if a node is in congress
    function isInCongress(address addr) public view returns (bool) {
        return members.contains(addr);
    }

    // get numbers of congress's member
    function getCongressNum() public view returns (uint256) {
        return members.values.length;
    }

    // get all addresses of congress
    function getCongress() public view returns (address[]) {
        return members.getAll();
    }
}
