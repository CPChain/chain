pragma solidity ^0.4.0;

// TODO this file exposes security holes.

contract Campaign {

    address owner;
    uint public viewIdx = 0;

    uint public baseDeposit = 50;
    uint public minimumRpt = 50;

    uint public minimumNoc = 1;
    uint public maximumNoc = 10;

    struct CandidateInfo {
        uint numOfCampaign;
        uint deposit;
        uint timestamp;
    }

    mapping(address => CandidateInfo) public candidates;
    mapping(uint => address[]) public campaignSnapshots;

    constructor() public {
        owner = msg.sender;
    }
    
    function ClaimCampaign(uint num_of_campaign, uint rpt) public payable {
        require(rpt >= minimumRpt, "too low rpt.");
        require((num_of_campaign >= minimumNoc && num_of_campaign <= maximumNoc), "num of campaign out of range.");
        require(msg.value == baseDeposit * num_of_campaign, "wrong deposit value.");

        address candidate = msg.sender;

        // require(candidates[candidate].numOfCampaign == 0, "already claimed campaign.");

        // set candidate info.
        if (candidates[candidate].numOfCampaign == 0){
            candidates[candidate] = CandidateInfo(num_of_campaign, msg.value, block.timestamp);
        } else {
            candidates[candidate].numOfCampaign += num_of_campaign;
            candidates[candidate].deposit += msg.value;
            candidates[candidate].timestamp = block.timestamp;
        }

        // add candidate to campaignSnapshots.
        for(uint i = viewIdx; i < viewIdx + num_of_campaign; i++) {
            campaignSnapshots[i].push(candidate);
        }
    }

    // TODO QuitCampaign
    function QuitCampaign() public payable {
        address candidate = msg.sender;
        require(candidates[candidate].numOfCampaign > 0, "already quit campaign.");

        candidates[candidate] = CandidateInfo(0, 0, block.timestamp);

        candidate.transfer(candidates[candidate].deposit);

        // remove candidate from current view snapshot
        for(uint i = 0; i < campaignSnapshots[viewIdx].length; i++) {
            if (campaignSnapshots[viewIdx][i] == candidate) {
                // TODO delete element from array
                // delete campaignSnapshots[viewIdx][candidate];
            }
        }
    }

    function CandidatesOf(uint view_idx) public view returns (address[]){
        return campaignSnapshots[view_idx];
    }

    function CandidateInfoOf(address candidate) public view returns (uint, uint, uint) {
        return (candidates[candidate].numOfCampaign, candidates[candidate].deposit, candidates[candidate].timestamp);
    }

    // TODO. add restriction that only last commissioner can call this with require statement.
    function ViewChange() public {
        for(uint i = 0; i < campaignSnapshots[viewIdx].length; i++){
            address candidate = campaignSnapshots[viewIdx][i];
            if(candidates[candidate].deposit >= baseDeposit){
                candidates[candidate].deposit -= baseDeposit;
                campaignSnapshots[viewIdx][i].transfer(baseDeposit);
            }
        }
        viewIdx = viewIdx + 1;
    }

    // TODO. require sender check.
    // function punishCandidate(address candidate) public {
    //     require(candidates[candidate].deposit >= baseDeposit, "wrong deposit value.");
    //     candidates[candidate].deposit -= baseDeposit;
    // }

}
