/**
 * campaign contract is used for rnodes to claim campaign.
 * the general campaign process is as follows:
 * 1. nodes submit parameters(numOfCampaign) and proofs, including memory and cpu proofs.
 * 2. each proof consists of an address, a nonce and a block number(hash);
 * 3. 'address' prevents nodes from stealing others' proof, 'block hash' avoids calculation in advance;
 * 4. campaign contract checks if all requirements are satisfied:
 *    rnode, admission and parameters
 * 5. if pass, nodes become candidate.
**/


pragma solidity ^0.4.24;

import "./lib/safeMath.sol";

// there are two interfaces to interact with admission and rnode contracts
// rnode and admission contracts must be deployed before this campaign contract, because
// addresses of rnode and admission contracts are needed to initiate interfaces during construction of campaign contract
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

contract RnodeInterface{
    function isRnode(address _addr)public view returns (bool);
}


// TODO this file exposes security holes.

contract Campaign {

    using SafeMath for uint;

    address owner; // owner has permission to set parameters
    uint public termIdx = 0; // current term
    uint public viewLen = 3; // view length: the number of blocks it can propose within a term
    uint public termLen =12; // term length: the number of proposers in a certain term
    // 'round' is same with 'term'.
    uint public numPerRound = termLen * viewLen; // total number of blocks produced in a term.
    // a node must choose the number of terms when it claims campaign
    uint public minNoc = 1; // minimal number of terms
    uint public maxNoc = 10; //maximum number of terms
    uint public acceptableBlocks = 10; // only latest 10 blocks based proofs will be accepted
    uint public supportedVersion = 1; // only nodes with new version can claim campaign

    // a new type for a single candidate
    struct CandidateInfo {
        uint numOfCampaign; // total number of terms
        uint startTermIdx;
        uint stopTermIdx;
    }

    mapping(address => CandidateInfo) candidates; // store a 'CandidateInfo' struct for each possible address
    mapping(uint => address[]) campaignSnapshots; // store all candidates for each term

    // declare admission and rnode interfaces
    AdmissionInterface admission;
    RnodeInterface    rnode;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    event ClaimCampaign(address candidate, uint startTermIdx, uint stopTermIdx);

    // admission and rnode interfaces will be initiated during creation of campaign contract
    constructor(address _admissionAddr, address _rnodeAddr) public {
        owner = msg.sender;
        admission = AdmissionInterface(_admissionAddr);
        rnode = RnodeInterface(_rnodeAddr);
    }

    function() payable public { revert(); }

    // get all candidates of given term index
    function candidatesOf(uint _termIdx) public view returns (address[]){
        return campaignSnapshots[_termIdx];
    }

    // get info of given candidate
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

    // admission interface can be set afterwards by owner
    function setAdmissionAddr(address _addr) public onlyOwner {
        admission = AdmissionInterface(_addr);
    }

    // rnode interface can be set afterwards by owner
    function setRnodeInterface(address _addr) public onlyOwner {
        rnode = RnodeInterface(_addr);
    }

    // owner can set these parameters
    function updateMinNoc(uint _minNoc) public onlyOwner {
        minNoc = _minNoc;
    }

    function updateMaxNoc(uint _maxNoc) public onlyOwner {
        maxNoc = _maxNoc;
    }

    function updateTermLen(uint _termLen) public onlyOwner {
        termLen = _termLen;
        numPerRound = SafeMath.mul(termLen, viewLen);
    }

    function updateViewLen(uint _viewLen) public onlyOwner {
        viewLen = _viewLen;
        numPerRound = SafeMath.mul(termLen, viewLen);
    }

    function updateAcceptableBlocks(uint _acceptableBlocks) public onlyOwner {
        acceptableBlocks = _acceptableBlocks;
    }

    function updateSupportedVersion(uint _supportedVersion) public onlyOwner {
        supportedVersion = _supportedVersion;
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

    // claim campaign will verify these parameters, if pass, the node will become candidate
    function claimCampaign(
        uint _termsToCampaign,  // number of terms that the node want to claim campaign

        // admission parameters
        uint64 _cpuNonce,
        uint _cpuBlockNumber,
        uint64 _memoryNonce,
        uint _memoryBlockNumber,
        uint version
    )
    public
    {
        // get current term, update termIdx
        updateTermIdx();

        require(version >= supportedVersion);

        // proofs must be calculated based on latest blocks
        if(block.number > acceptableBlocks) {
            require(_cpuBlockNumber >= block.number.sub(acceptableBlocks) && _memoryBlockNumber >= block.number.sub(acceptableBlocks));
        }
        // only rnode can become candidate
        require(rnode.isRnode(msg.sender)==true, "not RNode by rnode");

        // verify the sender's cpu&memory ability.
        require(admission.verify(_cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, msg.sender), "cpu or memory not passed.");
        require((_termsToCampaign >= minNoc && _termsToCampaign <= maxNoc), "num of campaign out of range.");

        address candidate = msg.sender;

        // if nodes have not ended their terms, they can not claim again
        require(
            candidates[candidate].stopTermIdx <= termIdx,
            "please waite until your last round ended and try again."
        );

        // set candidate's numOfCampaign according to arguments, and set start and end termIdx respectively
        candidates[candidate].numOfCampaign =candidates[candidate].numOfCampaign.add(_termsToCampaign);
        candidates[candidate].startTermIdx = termIdx.add(1);

        //[start, stop]
        candidates[candidate].stopTermIdx = candidates[candidate].startTermIdx.add(_termsToCampaign.sub(1));

        // add candidate to campaignSnapshots.
        for(uint i = candidates[candidate].startTermIdx; i <= candidates[candidate].stopTermIdx; i++) {
            campaignSnapshots[i].push(candidate);
        }
        emit ClaimCampaign(candidate, candidates[candidate].startTermIdx, candidates[candidate].stopTermIdx);
    }

    /** update termIdx called by function ClaimCampaign. */
    function updateTermIdx() internal {
        uint blockNumber = block.number;
        if (blockNumber == 0) {
            termIdx = 0;
            return;
        }

        // calculate current term
        termIdx = (blockNumber.sub(1)).div(numPerRound);
    }

}
