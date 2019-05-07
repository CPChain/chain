pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Rnode {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    uint256 public period = 1 minutes;
    uint256 public rnodeThreshold = 200000 ether;
    Set.Data private rnodes;

    struct Participant {
        uint256 lockedDeposit;
        uint256 lockedTime;
    }

    mapping (address => Participant) public Participants;

    event NewRnode(address who, uint256 lockedDeposit, uint256 lockedTime);
    event RnodeQuit(address who);

    modifier onlyOwner() {require(msg.sender == owner);_;}

    constructor () public {
        owner = msg.sender;
    }

    function joinRnode() public payable {
        require(!isContract(msg.sender),"please not use contract call this function");
        require(!rnodes.contains(msg.sender));
        require(msg.value >= rnodeThreshold);

        Participants[msg.sender].lockedDeposit = Participants[msg.sender].lockedDeposit.add(msg.value);
        Participants[msg.sender].lockedTime = block.timestamp;

        rnodes.insert(msg.sender);

        emit NewRnode(msg.sender, Participants[msg.sender].lockedDeposit, Participants[msg.sender].lockedTime);
    }

    function quitRnode() public {
        require(rnodes.contains(msg.sender));
        require(Participants[msg.sender].lockedTime + period <= block.timestamp);

        msg.sender.transfer(Participants[msg.sender].lockedDeposit);
        Participants[msg.sender].lockedDeposit = 0;

        rnodes.remove(msg.sender);

        emit RnodeQuit(msg.sender);
    }

    function setPeriod(uint256 _period) public onlyOwner() {
        period = _period;
    }

    function setRnodeThreshold(uint256 threshold) public onlyOwner() {
        rnodeThreshold = threshold;
    }

    function isContract(address addr) public view returns (bool) {
        uint size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    function isRnode(address addr) public view returns (bool) {
        return rnodes.contains(addr);
    }

    function getRnodeNum() public view returns (uint256) {
        return rnodes.values.length;
    }

    function getRnodes() public view returns (address[]) {
        return rnodes.getAll();
    }
}