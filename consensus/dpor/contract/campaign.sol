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
    mapping(uint => address[]) public campaignHistory;

    constructor() public {
        owner = msg.sender;
    }
    
    function ClaimCampaign(uint num_of_campaign, uint rpt) public payable {
        require(rpt >= minimumRpt, "too low rpt.");
        require((num_of_campaign >= minimumNoc && num_of_campaign <= maximumNoc), "num of campaign out of range.");
        require(msg.value == baseDeposit * num_of_campaign, "wrong deposit value.");

        address candidate = msg.sender;

        require(candidates[candidate].numOfCampaign == 0, "already claimed campaign.");

        // set candidate info.
        candidates[candidate] = CandidateInfo(num_of_campaign, msg.value, block.timestamp);

        // add candidate to campaignHistory.
        for(uint i = viewIdx; i < viewIdx + num_of_campaign; i++) {
            campaignHistory[i].push(candidate);
        }
    }

    function CandidatesOf(uint view_idx) public view returns (address[]){
        return campaignHistory[view_idx];
    }

    function CandidateInfoOf(address candidate) public view returns (uint, uint, uint) {
        return (candidates[candidate].numOfCampaign, candidates[candidate].deposit, candidates[candidate].timestamp);
    }

    // TODO. add restriction that only last commissioner can call this with require statement.
    function ViewChange() public {
        for(uint i = 0; i < campaignHistory[viewIdx].length; i++){
            address candidate = campaignHistory[viewIdx][i];
            if(candidates[candidate].deposit >= baseDeposit){
                candidates[candidate].deposit -= baseDeposit;
                campaignHistory[viewIdx][i].transfer(baseDeposit);
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
