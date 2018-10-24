pragma solidity ^0.4.24;

/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {

  /**
  * @dev Multiplies two numbers, throws on overflow.
  */
  function mul(uint256 a, uint256 b) internal pure returns (uint256) {
    if (a == 0) {
      return 0;
    }
    uint256 c = a * b;
    assert(c / a == b);
    return c;
  }

  /**
  * @dev Integer division of two numbers, truncating the quotient.
  */
  function div(uint256 a, uint256 b) internal pure returns (uint256) {
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }

  /**

  * @dev Subtracts two numbers, throws on overflow (i.e. if subtrahend is greater than minuend).

  */


  // SUB function is not necessary for cpc
  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    assert(b <= a);
    return a - b;
  }

  /**
  * @dev Adds two numbers, throws on overflow.
  */
  function add(uint256 a, uint256 b) internal pure returns (uint256) {
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}


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


contract AdmissionInterface {
    function verify(uint64 _cpuNonce, uint _cpuBlockNumber, uint64 _memoryNonce, uint _memoryBlockNumber) public constant returns (bool);
}



// TODO this file exposes security holes.

contract Campaign {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    uint public viewIdx = 0;
    uint public numPerRound = 21;
    uint public baseDeposit = 50;
    uint public minimumRpt = 50;

    uint public minimumNoc = 1;
    uint public maximumNoc = 10;

    struct CandidateInfo {
        uint numOfCampaign;
        uint deposit;
        uint startViewIdx;
        uint stopViewIdx;
    }

    mapping(address => CandidateInfo) candidates;
    mapping(uint => Set.Data) campaignSnapshots;
    AdmissionInterface admission;

    modifier onlyOwner(){require(msg.sender == owner);_;}

    constructor() public {
        owner = msg.sender;
    }

    /*
    set the Admission interface address.
    */
    function setAdmissionAddr(address _addr) public onlyOwner(){
        admission = AdmissionInterface(_addr);
    }

    /*
        update the config params.
    */
    function updateBaseDeposit(uint _deposit) public onlyOwner(){
        baseDeposit = _deposit;
    }

    function updateMinimumNoc(uint _minimumNoc) public onlyOwner(){
        minimumNoc = _minimumNoc;
    }

    function updateMaximumNoc(uint _maximumNoc) public onlyOwner(){
        maximumNoc = _maximumNoc;
    }

    /*
        Claim a Candidate have two conditions.
        One is pay some specified pcp.
        The other is pass the cpu&memory capacity verification.

        Each call may tried to update viewIdx once.
    */
    function claimCampaign(
        uint num_of_campaign,
        uint rpt,
        uint64 _cpuNonce,
        uint _cpuBlockNumber,
        uint64 _memoryNonce,
        uint _memoryBlockNumber
        )
        public
        payable {
            require(rpt >= minimumRpt, "too low rpt.");
            require(msg.value == SafeMath.mul(baseDeposit, num_of_campaign), "wrong deposit value.");
            // verify the sender's cpu ability.
            require(admission.verify(_cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber), "cpu or memory verify falure.");
            address candidate = msg.sender;
            updateViewIdx();

            require(candidates[candidate].stopViewIdx <= viewIdx, "please waite until your last round and try again.");
            require((num_of_campaign >= minimumNoc && num_of_campaign <= maximumNoc), "num of campaign out of range.");

            candidates[candidate].numOfCampaign = candidates[candidate].numOfCampaign.add(num_of_campaign);
            candidates[candidate].deposit = candidates[candidate].deposit.add(msg.value);
            candidates[candidate].startViewIdx = viewIdx.add(1);
            candidates[candidate].stopViewIdx = viewIdx.add(num_of_campaign);
            // add candidate to campaignSnapshots.
            for(uint i = candidates[candidate].startViewIdx; i < candidates[candidate].startViewIdx.add(num_of_campaign); i++) {
                campaignSnapshots[i].insert(candidate);
            }
        }

    // update viewIdx called by function ClaimCampaign.
    function updateViewIdx() internal{
        uint blockNumber = block.number;
        viewIdx = blockNumber / numPerRound;
    }

    // TODO QuitCampaign
    function quitCampaign() public {
        address candidate = msg.sender;
        require(candidates[candidate].numOfCampaign > 0, "already quit campaign.");
        // remove candidate from current view snapshot
        for(uint i = viewIdx.add(1); i < candidates[candidate].stopViewIdx.add(1); i++) {
            // if(candidates[candidate].deposit >= baseDeposit){
            //     candidates[candidate].deposit -= baseDeposit;
            //     candidate.transfer(baseDeposit);
            // }
            campaignSnapshots[i].remove(candidate);
        }
        uint deposit = candidates[candidate].deposit;
        candidates[candidate].numOfCampaign = 0;
        candidates[candidate].deposit = 0;
        candidates[candidate].startViewIdx = 0;
        candidates[candidate].stopViewIdx = 0;
        candidate.transfer(deposit);
    }

    function candidatesOf(uint view_idx) public view returns (address[]){
        return campaignSnapshots[view_idx].values;
    }

    function candidateInfoOf(address candidate)
        public
        view
        returns (
            uint,
            uint,
            uint,
            uint
        ) {
            return (
                candidates[candidate].numOfCampaign,
                candidates[candidate].deposit,
                candidates[candidate].startViewIdx,
                candidates[candidate].stopViewIdx);
        }

    // TODO. add restriction that only last commissioner can call this with require statement.
    // function ViewChange() public payable {
    //     for(uint i = 0; i < campaignSnapshots[viewIdx].values.length; i++){
    //         address candidate = campaignSnapshots[viewIdx].values[i];
    //         if(candidates[candidate].deposit >= baseDeposit){
    //             candidates[candidate].deposit -= baseDeposit;
    //             candidate.transfer(baseDeposit);
    //         }
    //     }
    //     viewIdx = viewIdx + 1;
    // }

    // TODO. require sender check.
    // function punishCandidate(address candidate) public {
    //     require(candidates[candidate].deposit >= baseDeposit, "wrong deposit value.");
    //     candidates[candidate].deposit -= baseDeposit;
    // }

}
