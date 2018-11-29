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
    uint public viewIdx = 0;
    // 21 candidates and 21 blocks per round.
    uint public numPerRound = 12; // @AC use termLen * viewLen instead of hardcoded 21
    // 50 wei per round.
    uint public baseDeposit = 50;
    // The minimun and maximun round to claim.
    uint public minNoc = 1;
    uint public maxNoc = 10;
    // withdraw deposit after each round.
    uint withdrawViewIdx = 0;

    struct CandidateInfo {
        uint numOfCampaign;
        uint deposit;
        uint startViewIdx;
        uint stopViewIdx;
        // recorded for ViewChange
        uint baseDeposit;
    }

    mapping(address => CandidateInfo) candidates;
    mapping(uint => Set.Data) campaignSnapshots;

    AdmissionInterface admission;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    // TODO add some log.
    event ClaimCampaign(address candidate, uint startViewIdx, uint stopViewIdx);
    event QuitCampaign(address candidate, uint payback);
    event ViewChange();

    constructor(address _addr) public {
        owner = msg.sender;
        admission = AdmissionInterface(_addr);
    }

    function() payable public { }

    function candidatesOf(uint _viewIdx) public view returns (address[]){
        return campaignSnapshots[_viewIdx].values;
    }

    function candidateInfoOf(address _candidate)
        public
        view
        returns (uint, uint, uint, uint)
    {
        return (
            candidates[_candidate].numOfCampaign,
            candidates[_candidate].deposit,
            candidates[_candidate].startViewIdx,
            candidates[_candidate].stopViewIdx
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
     * Each call may tried to update viewIdx once.
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
        updateViewIdx();
        require(
            candidates[candidate].numOfCampaign == 0,
            "please waite until your last round ended and try again."
        );
        require((_numOfCampaign >= minNoc && _numOfCampaign <= maxNoc), "num of campaign out of range.");

        address candidate = msg.sender;

        candidates[candidate].numOfCampaign = candidates[candidate].numOfCampaign.add(_numOfCampaign);
        candidates[candidate].deposit = candidates[candidate].deposit.add(msg.value);
        candidates[candidate].startViewIdx = viewIdx.add(1);
        //[start, stop)
        candidates[candidate].stopViewIdx = candidates[candidate].startViewIdx.add(_numOfCampaign);
        candidates[candidate].baseDeposit = baseDeposit;
        // add candidate to campaignSnapshots.
        for(uint i = candidates[candidate].startViewIdx; i < candidates[candidate].stopViewIdx; i++) {
            campaignSnapshots[i].insert(candidate);
        }
        emit ClaimCampaign(candidate, candidates[candidate].startViewIdx, candidates[candidate].stopViewIdx);
    }

    // TODO QuitCampaign test ok.
    function quitCampaign() public {
        address candidate = msg.sender;
        require(candidates[candidate].numOfCampaign > 0, "already quit campaign or no need to quit.");
        updateViewIdx();
        // require(candidates[candidate].stopViewIdx > viewIdx.add(1), "too late to quit campaign");
        // remove candidate from current view snapshot
        for(uint i = viewIdx.add(1); i < candidates[candidate].stopViewIdx; i++) {
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
        updateViewIdx();
        require(withdrawViewIdx < viewIdx, "Nothing can withdraw. Please wait until this view is finished.");
        uint size;
        for(; withdrawViewIdx < viewIdx; withdrawViewIdx++) {
            // avoid recalculate the size for circulation times.
            size = campaignSnapshots[withdrawViewIdx].values.length;
            for(uint i = 0; i < size; i++) {
                address candidate = campaignSnapshots[viewIdx].values[i];
                uint depositValue = candidates[candidate].baseDeposit;
                if(candidates[candidate].deposit >= depositValue) {
                    candidates[candidate].deposit -= depositValue;
                    candidate.transfer(depositValue);
                    candidates[candidate].numOfCampaign--;
                }
                // if candidate's tenure is all over, all status return to zero.
                if (candidates[candidate].numOfCampaign == 0) {
                    candidates[candidate].startViewIdx = 0;
                    candidates[candidate].stopViewIdx = 0;
                    candidates[candidate].baseDeposit = 0;
                }
            }
        }
    }

    /** update viewIdx called by function ClaimCampaign. */
    function updateViewIdx() internal{
        uint blockNumber = block.number;
        viewIdx = blockNumber / numPerRound;
    }

    // TODO. require sender check.
    function punishCandidate(address candidate, uint _viewIdx) public onlyOwner {
        uint depositValue = candidates[candidate].baseDeposit;
        require(candidates[candidate].deposit >= depositValue, "wrong deposit value.");
        candidates[candidate].deposit -= depositValue;
        campaignSnapshots[_viewIdx].remove(candidate);
    }

    function paybackDeposit(address candidate) internal {
        uint deposit = candidates[candidate].deposit;
        candidates[candidate].numOfCampaign = 0;
        candidates[candidate].deposit = 0;
        candidates[candidate].startViewIdx = 0;
        candidates[candidate].stopViewIdx = 0;
        candidate.transfer(deposit);
    }

}
