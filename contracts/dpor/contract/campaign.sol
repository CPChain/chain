pragma solidity ^0.4.24;

library Set {
    // We define a new struct datatype that will be used to
    // hold its data in the calling contract.
    struct Data {
        mapping(address => bool) flags;
        address[] values;
    }

    // Note that the first parameter is of type "storage
    // reference" and thus only its storage address and not
    // its contents is passed as part of the call.  This is a
    // special feature of library functions.  It is idiomatic
    // to call the first parameter 'self', if the function can
    // be seen as a method of that object.
    function insert(Data storage self, address value)
      internal returns (bool)
    {
        if (self.flags[value])
            return false; // already there
        self.flags[value] = true;
        self.values.push(value);
        return true;
    }

    function remove(Data storage self, address value)
       internal returns (bool)
    {
        if (!self.flags[value])
            return false; // not there
        self.flags[value] = false;

        for (uint i = 0 ; i < self.values.length ; i++){
            if (self.values[i] == value){
                for (uint j = i; j<self.values.length-1; j++){
                    self.values[j] = self.values[j+1];
                }
                delete self.values[self.values.length-1];
                self.values.length--;
                break;
            }
        }
        return true;
    }

    function contains(Data storage self, address value)
       internal view returns (bool)
    {
        return self.flags[value];
    }

    function getAll(Data storage self)
       internal view returns (address[])
    {
        return self.values;
    }
}

// TODO this file exposes security holes.

contract Campaign {
    using Set for Set.Data;

    address owner;
    uint public viewIdx = 0;

    uint public baseDeposit = 50;
    uint public minimumRpt = 50;

    uint public minimumNoc = 1;
    uint public maximumNoc = 10;

    struct CandidateInfo {
        uint numOfCampaign;
        uint deposit;
        uint startViewIdx;
    }

    mapping(address => CandidateInfo) candidates;
    mapping(uint => Set.Data) campaignSnapshots;

    constructor() public {
        owner = msg.sender;
    }
    
    function ClaimCampaign(uint num_of_campaign, uint rpt) public payable {
        require(rpt >= minimumRpt, "too low rpt.");
        require(msg.value == baseDeposit * num_of_campaign, "wrong deposit value.");

        address candidate = msg.sender;

        // set candidate info.
        if (candidates[candidate].numOfCampaign == 0){
            require((num_of_campaign >= minimumNoc && num_of_campaign <= maximumNoc), "num of campaign out of range.");
            candidates[candidate] = CandidateInfo(num_of_campaign, msg.value, viewIdx);
        } else {
            require((candidates[candidate].numOfCampaign + num_of_campaign >= minimumNoc && candidates[candidate].numOfCampaign + num_of_campaign <= maximumNoc), "num of campaign out of range.");
            candidates[candidate].numOfCampaign += num_of_campaign;
            candidates[candidate].deposit += msg.value;
        }

        // add candidate to campaignSnapshots.
        for(uint i = candidates[candidate].startViewIdx; i < candidates[candidate].startViewIdx + num_of_campaign; i++) {
            campaignSnapshots[i].insert(candidate);
        }
    }

    // TODO QuitCampaign
    function QuitCampaign() public payable {
        address candidate = msg.sender;
        require(candidates[candidate].numOfCampaign > 0, "already quit campaign.");
        // remove candidate from current view snapshot
        for(uint i = viewIdx; i < candidates[candidate].startViewIdx + candidates[candidate].numOfCampaign; i++) {
            if(candidates[candidate].deposit >= baseDeposit){
                candidates[candidate].deposit -= baseDeposit;
                candidate.transfer(baseDeposit);
            }
            campaignSnapshots[i].remove(candidate);
        }
        candidates[candidate].numOfCampaign = 0;
    }

    function CandidatesOf(uint view_idx) public view returns (address[]){
        return campaignSnapshots[view_idx].values;
    }

    function CandidateInfoOf(address candidate) public view returns (uint, uint, uint) {
        return (candidates[candidate].numOfCampaign, candidates[candidate].deposit, candidates[candidate].startViewIdx);
    }

    // TODO. add restriction that only last commissioner can call this with require statement.
    function ViewChange() public payable {
        for(uint i = 0; i < campaignSnapshots[viewIdx].values.length; i++){
            address candidate = campaignSnapshots[viewIdx].values[i];
            if(candidates[candidate].deposit >= baseDeposit){
                candidates[candidate].deposit -= baseDeposit;
                candidate.transfer(baseDeposit);
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
