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


// TODO this file exposes security holes.

contract Campaign {

    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    // The current round number.
    uint public termIdx = 0;
    // 21 candidates and 21 blocks per round.
    uint public numPerRound = 12; // @AC use termLen * viewLen instead of hardcoded 21
    // 50 wei per round.
    uint public baseDeposit = 50;
    // The minimun and maximun round to claim.
    uint public minNoc = 1;
    uint public maxNoc = 10;
    // withdraw deposit after each round.
    uint withdrawTermIdx = 0;

    struct CandidateInfo {
        uint numOfCampaign;
        uint deposit;
        uint startTermIdx;
        uint stopTermIdx;
        // recorded for ViewChange
        uint baseDeposit;
    }

    mapping(address => CandidateInfo) candidates;
    mapping(uint => Set.Data) campaignSnapshots;

    AdmissionInterface admission;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    // TODO add some log.
    event ClaimCampaign(address candidate, uint startTermIdx, uint stopTermIdx);
    event QuitCampaign(address candidate, uint payback);
    event ViewChange();

    constructor(address _addr) public {
        owner = msg.sender;
        admission = AdmissionInterface(_addr);
    }

    function() payable public { }

    function candidatesOf(uint _termIdx) public view returns (address[]){
        return campaignSnapshots[_termIdx].values;
    }

    function candidateInfoOf(address _candidate)
        public
        view
        returns (uint, uint, uint, uint)
    {
        return (
            candidates[_candidate].numOfCampaign,
            candidates[_candidate].deposit,
            candidates[_candidate].startTermIdx,
            candidates[_candidate].stopTermIdx
        );
    }

    /** set the Admission interface address. */
    function setAdmissionAddr(address _addr) public onlyOwner(){
        admission = AdmissionInterface(_addr);
    }

    /** update the config params. */
    function updateBaseDeposit(uint _deposit) public onlyOwner(){
        baseDeposit = _deposit;
    }

    function updateMinNoc(uint _minNoc) public onlyOwner(){
        minNoc = _minNoc;
    }

    function updateMaxNoc(uint _maxNoc) public onlyOwner(){
        maxNoc = _maxNoc;
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
        require(msg.value == SafeMath.mul(baseDeposit, _numOfCampaign), "wrong deposit value.");
        // verify the sender's cpu&memory ability.
        require(admission.verify(_cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, msg.sender), "cpu or memory not passed.");
        require((_numOfCampaign >= minNoc && _numOfCampaign <= maxNoc), "num of campaign out of range.");
        require(
            candidates[candidate].numOfCampaign == 0,
            "please waite until your last round ended and try again."
        );

        updateTermIdx();

        address candidate = msg.sender;

        candidates[candidate].numOfCampaign = _numOfCampaign;
        candidates[candidate].deposit = SafeMath.mul(baseDeposit, _numOfCampaign);
        candidates[candidate].startTermIdx = termIdx.add(1);

        //[start, stop)
        candidates[candidate].stopTermIdx = candidates[candidate].startTermIdx.add(_numOfCampaign);
        candidates[candidate].baseDeposit = baseDeposit;

        // add candidate to campaignSnapshots.
        for(uint i = candidates[candidate].startTermIdx; i < candidates[candidate].stopTermIdx; i++) {
            campaignSnapshots[i].insert(candidate);
        }
        emit ClaimCampaign(candidate, candidates[candidate].startTermIdx, candidates[candidate].stopTermIdx);
    }

    // TODO QuitCampaign test ok.
    function quitCampaign() public {
        address candidate = msg.sender;
        require(candidates[candidate].numOfCampaign > 0, "already quit campaign or no need to quit.");
        updateTermIdx();
        // require(candidates[candidate].stopTermIdx > termIdx.add(1), "too late to quit campaign");
        // remove candidate from current view snapshot
        for(uint i = termIdx.add(1); i < candidates[candidate].stopTermIdx; i++) {
            campaignSnapshots[i].remove(candidate);
        }
        paybackDeposit(candidate);
    }

    // TODO. add restriction that only last commissioner can call this with require statement.
    /**
     * CPC master will call this function at regular intervals.
     * Also anyone others can call this function to withdraw money for everyone if he is willing to pay the gas.
     */
    // TODO test fail.
    function viewChange() public payable {
        updateTermIdx();
        require(withdrawTermIdx < termIdx, "Nothing can withdraw. Please wait until this view is finished.");
        uint size;
        for(; withdrawTermIdx < termIdx; withdrawTermIdx++) {
            // avoid recalculate the size for circulation times.
            size = campaignSnapshots[withdrawTermIdx].values.length;
            for(uint i = 0; i < size; i++) {
                address candidate = campaignSnapshots[termIdx].values[i];

                if (candidates[candidate].numOfCampaign == 0) {
                    continue;
                }

                uint depositValue = 0;
                if(candidates[candidate].deposit >= candidates[candidate].baseDeposit) {
                    depositValue = candidates[candidate].baseDeposit;
                }
                else {
                    depositValue = candidates[candidate].deposit;
                }

                candidates[candidate].deposit = SafeMath.sub(candidates[candidate].deposit, depositValue);
                candidates[candidate].numOfCampaign = SafeMath.sub(candidates[candidate].numOfCampaign, 1);
                candidate.transfer(depositValue);

                // if candidate's tenure is all over, all status return to zero.
                if (candidates[candidate].numOfCampaign == 0) {
                    candidates[candidate].startTermIdx = 0;
                    candidates[candidate].stopTermIdx = 0;
                    candidates[candidate].baseDeposit = 0;
                }
            }
        }
    }

    /** update termIdx called by function ClaimCampaign. */
    function updateTermIdx() internal{
        uint blockNumber = block.number;
        termIdx = (blockNumber - 1) / numPerRound;
    }

    // TODO. require sender check.
    function punishCandidate(address candidate, uint _termIdx) public onlyOwner {
        uint depositValue = candidates[candidate].baseDeposit;
        require(candidates[candidate].deposit >= depositValue, "wrong deposit value.");
        candidates[candidate].deposit -= depositValue;
        campaignSnapshots[_termIdx].remove(candidate);
    }

    function paybackDeposit(address candidate) internal {
        uint deposit = candidates[candidate].deposit;
        candidates[candidate].numOfCampaign = 0;
        candidates[candidate].deposit = 0;
        candidates[candidate].startTermIdx = 0;
        candidates[candidate].stopTermIdx = 0;
        candidate.transfer(deposit);
    }

}
