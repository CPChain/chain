pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract AdmissionInterface {
    function verify(
        uint64 _cpuNonce,
        uint _cpuBlockNumber,
        uint64 _memoryNonce,
        uint _memoryBlockNumber,
        address _sender
        )
        public
        view
        returns (bool);
}

contract RewardInterface{
    function isCandidate(address _addr)public view returns (bool);
}


// TODO this file exposes security holes.

contract Campaign {

    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    // The current round number.
    uint public termIdx = 0;
    // The number of blocks it can propose is viewLen.
    uint public viewLen = 3;
    // The number of proposers in a certain term is termLen
    uint public termLen =4;
    // The sum of block in a term.
    uint public numPerRound = termLen * viewLen;
    // The minimun and maximun round to claim.
    uint public minNoc = 1;
    uint public maxNoc = 10;
    // withdraw deposit after each round.
    uint withdrawTermIdx = 0;

    struct CandidateInfo {
        uint numOfCampaign;
        uint startTermIdx;
        uint stopTermIdx;
    }

    mapping(address => CandidateInfo) candidates;
    mapping(uint => Set.Data) campaignSnapshots;

    AdmissionInterface admission;
    RewardInterface    reward;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    // TODO add some log.
    event ClaimCampaign(address candidate, uint startTermIdx, uint stopTermIdx);
    event QuitCampaign(address candidate, uint payback);
    event ViewChange();

    constructor(address _admissionAddr,address _rewardAddr) public {
        owner = msg.sender;
        admission = AdmissionInterface(_admissionAddr);
        reward = RewardInterface(_rewardAddr);
    }

    function() payable public { }

    function candidatesOf(uint _termIdx) public view returns (address[]){
        return campaignSnapshots[_termIdx].values;
    }

    function candidateInfoOf(address _candidate)
        public
        view
        returns (uint, uint, uint)
    {
        return (
            candidates[_candidate].numOfCampaign,
            candidates[_candidate].startTermIdx,
            candidates[_candidate].stopTermIdx
        );
    }

    /** set the Admission interface address. */
    function setAdmissionAddr(address _addr) public onlyOwner(){
        admission = AdmissionInterface(_addr);
    }
    /** set the Reward interface address. */
    function setRewardInterface(address _addr) public onlyOwner(){
        reward = RewardInterface(_addr);
    }

    function updateMinNoc(uint _minNoc) public onlyOwner(){
        minNoc = _minNoc;
    }

    function updateMaxNoc(uint _maxNoc) public onlyOwner(){
        maxNoc = _maxNoc;
    }

    function updateTermLen(uint _termLen) public onlyOwner(){
        termLen = _termLen;
        numPerRound = SafeMath.mul(termLen, viewLen);
    }

    function updateViewLen(uint _viewLen) public onlyOwner(){
        viewLen = _viewLen;
        numPerRound = SafeMath.mul(termLen, viewLen);
    }

    /**
     * Submits required information to participate the campaign for membership of the committee.
     *
     * Each call may tried to update termIdx once.
     *
     * Claiming a candidate has three conditions:
     * 1. pay some specified cpc token.
     * 2. pass the cpu&memory capacity proof.
     * 3. rpt score reaches the threshold (be computed somewhere else).
     */
    function claimCampaign(
        uint _numOfCampaign,
        uint64 _cpuNonce,
        uint _cpuBlockNumber,
        uint64 _memoryNonce,
        uint _memoryBlockNumber
        )
        public
        payable
    {
        // TODO: @ac once finishes pre-pay cpc for nodes to become candidates, enable the requirement checking below
        //require(reward.isRNode(msg.sender)==true, "not RNode by reward");
        // verify the sender's cpu&memory ability.
        require(admission.verify(_cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, msg.sender), "cpu or memory not passed.");
        require((_numOfCampaign >= minNoc && _numOfCampaign <= maxNoc), "num of campaign out of range.");

        updateCandidateStatus(); // update status first then check

        require(
            candidates[candidate].numOfCampaign == 0,
            "please waite until your last round ended and try again."
        );

        address candidate = msg.sender;

        candidates[candidate].numOfCampaign = _numOfCampaign;
        candidates[candidate].startTermIdx = termIdx.add(1);

        //[start, stop)
        candidates[candidate].stopTermIdx = candidates[candidate].startTermIdx.add(_numOfCampaign);

        // add candidate to campaignSnapshots.
        for(uint i = candidates[candidate].startTermIdx; i < candidates[candidate].stopTermIdx; i++) {
            campaignSnapshots[i].insert(candidate);
        }
        emit ClaimCampaign(candidate, candidates[candidate].startTermIdx, candidates[candidate].stopTermIdx);
    }

    /**
     * The function will be called when a node claims to campaign for proposer election to update candidates status.
     *
     */
    function updateCandidateStatus() public payable {
        updateTermIdx();
        if (withdrawTermIdx >= termIdx) {
            return;
        }

        uint size;
        for(; withdrawTermIdx < termIdx; withdrawTermIdx++) {
            // avoid recalculate the size for circulation times.
            size = campaignSnapshots[withdrawTermIdx].values.length;
            for(uint i = 0; i < size; i++) {
                address candidate = campaignSnapshots[termIdx].values[i];

                if (candidates[candidate].numOfCampaign == 0) {
                    continue;
                }

                candidates[candidate].numOfCampaign = SafeMath.sub(candidates[candidate].numOfCampaign, 1);

                // if candidate's tenure is all over, all status return to zero.
                if (candidates[candidate].numOfCampaign == 0) {
                    candidates[candidate].startTermIdx = 0;
                    candidates[candidate].stopTermIdx = 0;
                }
            }
        }
    }

    /** update termIdx called by function ClaimCampaign. */
    function updateTermIdx() internal{
        uint blockNumber = block.number;
        if (blockNumber == 0) {
            termIdx = 0;
            return;
        }
        termIdx = (blockNumber - 1).div(numPerRound);
    }

}
