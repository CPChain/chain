/**
 * rnode contract is for nodes to join and quit rnodes, and for campaign contract to check if a node is rnode
**/


pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Rnode {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner; // owner has permissions to modify parameters
    uint256 public period = 100 minutes; // rnode can withdraw deposit after period, owner can change period
    uint256 public rnodeThreshold = 200000 ether; // standard to become rnode, minimal amount, owner can change
    uint256 public supportedVersion = 1; // version control
    Set.Data private rnodes; // rnodes group
    // enabled indicates status of contract, only when it is true, nodes can join rnode.
    bool public enabled = true;

    // participant is a type of single rnode
    // record locked amount and start time for each rnode
    struct Participant {
        uint256 lockedDeposit;
        uint256 lockedTime;
    }

    // store a 'Participant' struct for each possible address
    mapping (address => Participant) public Participants;

    // new rnodes join, NewRnode will be emitted, containing 'who' locked 'how much' money at 'when'
    // rnodes quit, RnodeQuit will be emitted
    event NewRnode(address who, uint256 lockedDeposit, uint256 lockedTime);
    event RnodeQuit(address who);
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

    // there are there requirements for becoming rnodes:
    // 1. contract address can not become a rnode;
    // 2. rnodes can not deposit again;
    // 3. deposit money has to satisfy rnode threshold.
    function joinRnode(uint256 version) public payable onlyEnabled {
        require(version >= supportedVersion);
        require(!isContract(msg.sender),"please not use contract call this function");
        require(!rnodes.contains(msg.sender));
        require(msg.value >= rnodeThreshold);

        // if requirements above are satisfied, the node will be added into rnodes
        // lockedDeposit and lockedTime will be recorded in 'Participants'
        Participants[msg.sender].lockedDeposit = Participants[msg.sender].lockedDeposit.add(msg.value);
        Participants[msg.sender].lockedTime = block.timestamp;

        // the node will be inserted into rnodes group
        rnodes.insert(msg.sender);

        emit NewRnode(msg.sender, Participants[msg.sender].lockedDeposit, Participants[msg.sender].lockedTime);
    }

    // a node can quit rnodes anytime on conditions that:
    // 1. the node has to be in rnodes group;
    // 2. the node must quit after at least a period.
    function quitRnode() public {
        require(rnodes.contains(msg.sender));
        require(Participants[msg.sender].lockedTime + period <= block.timestamp);

        // if requirements above are satisfied, the node will receive locked deposit
        msg.sender.transfer(Participants[msg.sender].lockedDeposit);
        Participants[msg.sender].lockedDeposit = 0;

        // the node will be removed from rnodes group
        rnodes.remove(msg.sender);

        emit RnodeQuit(msg.sender);
    }

    // owner refunds one investor
    function refund(address investor) public onlyOwner {
        require(rnodes.contains(investor));
        uint256 amount = Participants[investor].lockedDeposit;
        investor.transfer(amount);
        Participants[investor].lockedDeposit = 0;
        rnodes.remove(investor);

        emit ownerRefund(investor, amount);
    }

    // owner refunds all investors
    function refundAll() public onlyOwner {
        uint256 num = rnodes.values.length;
        for(uint i=0; i<num; i++){
            address investor = rnodes.values[0];
            uint256 deposit = Participants[investor].lockedDeposit;
            investor.transfer(deposit);
            Participants[investor].lockedDeposit = 0;
            rnodes.remove(investor);

            emit ownerRefund(investor, deposit);
        }
        assert(rnodes.values.length == 0);

        emit ownerRefundAll(num);
    }

    // owner can enable and disable rnode contract
    function enableContract() public onlyOwner {
        enabled = true;
    }

    function disableContract() public onlyOwner {
        enabled = false;
    }

    // owner can set period, rnode threshold and supported version
    function setPeriod(uint256 _period) public onlyOwner {
        require(_period <= 1 days);
        period = _period;
    }

    function setRnodeThreshold(uint256 threshold) public onlyOwner {
        require(threshold >= 200000 ether);
        rnodeThreshold = threshold;
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

    // check if a node is rnode
    function isRnode(address addr) public view returns (bool) {
        return rnodes.contains(addr);
    }

    // get numbers of rnodes
    function getRnodeNum() public view returns (uint256) {
        return rnodes.values.length;
    }

    // get all addresses of rnodes
    function getRnodes() public view returns (address[]) {
        return rnodes.getAll();
    }
}