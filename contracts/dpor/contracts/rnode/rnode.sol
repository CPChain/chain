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
    uint256 public period = 1 minutes; // rnode can withdraw deposit after period, owner can change period
    uint256 public rnodeThreshold = 200000 ether; // standard to become rnode, minimal amount, owner can change
    Set.Data private rnodes; // rnodes group

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

    modifier onlyOwner() {require(msg.sender == owner);_;}

    constructor () public {
        owner = msg.sender;
    }

    // there are there requirements for becoming rnodes:
    // 1. contract address can not become a rnode;
    // 2. rnodes can not deposit again;
    // 3. deposit money has to satisfy rnode threshold.
    function joinRnode() public payable {
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

    // owner can set period and rnode threshold
    function setPeriod(uint256 _period) public onlyOwner() {
        period = _period;
    }

    function setRnodeThreshold(uint256 threshold) public onlyOwner() {
        rnodeThreshold = threshold;
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