
pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract CongressInterface{
    function isInCongress(address _addr)public view returns (bool);
    function getCongressNum() public view returns (uint256);
}

contract Proposal {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner; // owner has permissions to modify parameters
    uint256 public amountThreshold = 100 ether; // amount of pledge
    uint256 public approvalThreshold = 100; // threshold count of approval
    uint16 public voteThreshold = 67; // the ratio of the approved vote, 0%-100%
    uint256 public maxPeriod = 30 days; // max period
    uint16 public idLength = 36; // id length
    // enabled indicates status of contract, only when it is true, nodes can submit proposal
    bool public enabled = true;
    // can't submit proposals if the count of congress's member below minCongressMemberCount
    uint16 public minCongressMemberCount = 11;

    CongressInterface public congress;

    enum Status {
        Deposited,
        Approved,
        Successful,
        Timeout
    }

    struct ProposalItem {
        string id;
        uint256 lockedAmount;
        uint256 lockedTime;
        uint256 period;
        uint256 approvalCnt;
        uint256 voteCnt;
        address owner;
        Set.Data approvedAddr;
        Set.Data votedAddr;
        Status status;
        bool used;
    }

    mapping (string => ProposalItem) private proposals;
    string[] public proposalsIDList;

    // the '_' in modifier will be replaced by code in function;
    // if there are more than one modifiers in a function, '_' in first modifier will be replaced by code in second modifier
    // cf. https://ethereum.stackexchange.com/questions/29608/whats-the-order-of-execution-for-multiple-function-modifiers?rq=1
    modifier onlyOwner() {require(msg.sender == owner, "sender is not owner");_;}
    modifier onlyEnabled() {require(enabled, "contract is disabled");_;}
    modifier existsCheck(string id) {require(proposals[id].used, "ID is not exists");_;}
    modifier timeoutCheck(string id) {require(proposals[id].status != Status.Timeout && proposals[id].lockedTime + proposals[id].period > now,
        "This proposal is timeout");_;}

    event SubmitProposal(address who, string id, uint period, uint256 lockedAmount, uint256 lockedTime);
    event ApprovalProposal(address who, string id);
    event VoteProposal(address who, string id);
    event WithdrawMoney(address who, string id);
    event proposalTimeout(string id);
    event ownerRefund(string id);
    event ownerRefundAll();

    constructor (address _congressAddr) public {
        owner = msg.sender;
        congress = CongressInterface(_congressAddr);
    }

    // submit proposal
    function submit(string id, uint256 period) public payable onlyEnabled {
        require(congress.getCongressNum() >= minCongressMemberCount, "congress is not built now");
        require(period <= maxPeriod, "period should less than or equal to MaxPeriod");
        require(!proposals[id].used, "ID is already exists!");
        require(bytes(id).length > 0, "ID can't be empty");
        require(bytes(id).length == idLength, "ID is not equal to fixed length");
        require(msg.value >= amountThreshold, "deposit amount is less than threshold");

        proposals[id].id = id;
        proposals[id].lockedAmount = msg.value;
        proposals[id].lockedTime = block.timestamp;
        proposals[id].period = period;
        proposals[id].approvalCnt = 0;
        proposals[id].voteCnt = 0;
        proposals[id].owner = msg.sender;
        proposals[id].used = true;
        proposals[id].status = Status.Deposited;

        proposalsIDList.push(id);

        emit SubmitProposal(msg.sender, id, period, msg.value, block.timestamp);
    }

    // approval
    function approval(string id) public payable onlyEnabled existsCheck(id) timeoutCheck(id) {
        require(!proposals[id].approvedAddr.contains(msg.sender), "you have already approved this proposal");
        proposals[id].approvedAddr.insert(msg.sender);
        proposals[id].approvalCnt += 1;
        if (proposals[id].status == Status.Deposited) {
            if (proposals[id].approvalCnt >= approvalThreshold) {
                proposals[id].status = Status.Approved;
            }
        }
        emit ApprovalProposal(msg.sender, id);
    }

    // vote
    function vote(string id) public payable onlyEnabled existsCheck(id) timeoutCheck(id) {
        require(congress.isInCongress(msg.sender), "sender is not in congress");
        require(congress.getCongressNum() >= minCongressMemberCount, "congress is not built now");
        require(!proposals[id].votedAddr.contains(msg.sender), "you have already voted this proposal");
        require(proposals[id].status == Status.Approved || proposals[id].status == Status.Successful,
            "This proposal hasn't approved by the community");
        proposals[id].votedAddr.insert(msg.sender);
        proposals[id].voteCnt += 1;
        if (proposals[id].voteCnt * 100 / congress.getCongressNum() >= voteThreshold) {
            proposals[id].status = Status.Successful;
            _refund(id);
        }
        emit VoteProposal(msg.sender, id);
    }

    // withdraw
    function withdraw(string id) public payable existsCheck(id) {
        require(proposals[id].status == Status.Successful || proposals[id].status == Status.Timeout ||
            proposals[id].lockedTime + proposals[id].period <= now,
            "This proposal's status is not successful or timeout");
        require(proposals[id].lockedAmount > 0, "proposal's deposit has been withdrawn");
        require(proposals[id].owner == msg.sender, "the sender is not the owner of this proposal");
        if (proposals[id].status == Status.Deposited || proposals[id].status == Status.Approved) {
            if (proposals[id].lockedTime + proposals[id].period <= now) {
                // timeout
                proposals[id].status = Status.Timeout;
            }
        }
        msg.sender.transfer(proposals[id].lockedAmount);
        proposals[id].lockedAmount = 0;
        emit WithdrawMoney(msg.sender, id);
    }

    function refund(string id) public payable onlyOwner {
        require(proposals[id].lockedAmount > 0, "proposal's deposit has been withdrawn");
        _refund(id);
        emit ownerRefund(id);
    }

    function _refund(string id) internal existsCheck(id) {
        if (proposals[id].lockedAmount > 0) {
            proposals[id].owner.transfer(proposals[id].lockedAmount);
            proposals[id].lockedAmount = 0;
        }
    }

    function refundAll() public payable onlyOwner {
        require(enabled == false, "you should set enabled to false before refundAll");
        uint num = proposalsIDList.length;
        for(uint i = 0; i < num; i++) {
            _refund(proposalsIDList[i]);
        }
        emit ownerRefundAll();
    }

    function checkTimeout(string id) public payable existsCheck(id) {
        require(proposals[id].status != Status.Successful, "This proposal can not change because status is successful");
        require(proposals[id].status != Status.Timeout, "This proposal can not change because status is timeout");
        require(proposals[id].lockedTime + proposals[id].period <= now, "this proposal is not timeout");
        proposals[id].status = Status.Timeout;
        _refund(id);
        emit proposalTimeout(id);
    }

    // approval count
    function getApprovalCnt(string id) public view existsCheck(id) returns(uint256) {
        return proposals[id].approvalCnt;
    }

    // voted count
    function getVoteCnt(string id) public view existsCheck(id) returns(uint) {
        return proposals[id].voteCnt;
    }

    // status
    function getStatus(string id) public view existsCheck(id) returns(Status) {
        return proposals[id].status;
    }

    function getCongressNum() public view returns (uint256) {
        return congress.getCongressNum();
    }

    function getProposalsCnt() public view returns (uint) {
        return proposalsIDList.length;
    }

    // get deposited amount
    function getLockedAmount(string id) public view existsCheck(id) returns (uint256) {
        return proposals[id].lockedAmount;
    }

    // get deposited time
    function getLockedTime(string id) public view existsCheck(id) returns (uint256) {
        return proposals[id].lockedTime;
    }

    // get owner
    function getOwner(string id) public view existsCheck(id) returns (address) {
        return proposals[id].owner;
    }

    // get period
    function getPeriod(string id) public view existsCheck(id) returns (uint256) {
        return proposals[id].period;
    }

    // get approved address
    function getApprovedAddress(string id) public view existsCheck(id) returns (address[]) {
        return proposals[id].approvedAddr.getAll();
    }

    // get voted address
    function getVotedAddress(string id) public view existsCheck(id) returns (address[]) {
        return proposals[id].votedAddr.getAll();
    }

    // owner can enable and disable proposal contract
    function enableContract() public onlyOwner {
        enabled = true;
    }

    function disableContract() public onlyOwner {
        enabled = false;
    }

    function setMaxPeriod(uint256 period) public onlyOwner {
        maxPeriod = period;
    }

    // owner can set all threshold
    function setAmountThreshold(uint256 threshold) public onlyOwner {
        require(threshold >= 1 ether, "amount threshold should greater than or equal to 1 ether");
        amountThreshold = threshold;
    }

    function setApprovalThreshold(uint256 threshold) public onlyOwner {
        require(threshold >= 1, "approval threshold should greater than or equal to 1");
        approvalThreshold = threshold;
    }

    function setVoteThreshold(uint16 threshold) public onlyOwner {
        require(threshold >= 0, "vote threshold should greater than or equal 0");
        require(threshold <= 100, "vote threshold should less than 100");
        voteThreshold = threshold;
    }

    function setIDLength(uint16 length) public onlyOwner {
        require(length > 0, "length should greater than 0");
        require(length <= 256, "length should less than or equal to 256");
        idLength = length;
    }

    function setMinCongressMemberCount(uint16 number) public onlyOwner {
        require(number > 0, "length should greater than 0");
        minCongressMemberCount = number;
    }
}
