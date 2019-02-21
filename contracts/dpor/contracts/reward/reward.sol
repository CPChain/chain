pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Reward {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    bool private locked = true;
    uint256 public basicCriteria = 20000 ether;
    uint256 public electionCriteria = 200000 ether;
    uint256 public bonusPool = 1250000 ether; // 1.25m x 4 = 5m (cpc)
    uint256 public nextRound = 0;
    Set.Data internal rnodes;
    Set.Data internal participants;   // rnodes and enodes
    uint256 public nextRoundStartTime = 0;
    uint256 private period = 90 days;

    struct Investor {
        uint256 freeDeposit;
        uint256 lockedDeposit;
        uint256 returned;
        bool toRenew;
    }

    mapping (address => Investor) private investors;

    event SubmitDeposit(address who,uint256 value);
    event WithdrawDeposit(address who, uint256 value);
    event JoinPartcipant(address who, uint256 value);
    event JoinCandidates(address who, uint256 value);
    event TransferDeposit(address who, uint256 value);
    event NewRaise(uint256 round, bool lock,uint256 _bonusPool);
    event DepositInsufficient(address who,uint256 value);
    event ContinuedInvest(address _addr,bool _iscontinue);
    event FundBonusPool(uint256 value);

    modifier onlyOwner() {require(msg.sender == owner);_;}

    modifier unlocked() {
        require(locked == false);
        _;
    }

    constructor () public {
        owner = msg.sender;
    }

    function () public payable {
        emit FundBonusPool(msg.value);
    }

    function newRaise() public onlyOwner() {
        locked = false;
        emit NewRaise(nextRound,locked,bonusPool);
    }

    function setBonusPool(uint256 _bonus) public onlyOwner() {
        bonusPool = _bonus;
    }

    function submitDeposit() public payable unlocked() {
        require(!isContract(msg.sender),"please not use contract call this function");
        if (!isParticipant(msg.sender)){
            participants.insert(msg.sender);
        }
        investors[msg.sender].freeDeposit = investors[msg.sender].freeDeposit.add(msg.value);
        emit SubmitDeposit(msg.sender,msg.value);
    }

    function getTotalBalance(address _addr) public view returns (uint256){
        uint256 freeBalance=0;
        uint256 lockedBalance=0;
        freeBalance = investors[_addr].freeDeposit;
        lockedBalance = investors[_addr].lockedDeposit;
        return freeBalance.add(lockedBalance);
    }

    function getFreeBalance(address _addr) public view returns (uint256){
        uint256  deposit;
        deposit = investors[_addr].freeDeposit;
        return  deposit;
    }

    function getLockedBalance(address _addr) public view returns (uint256){
        uint256  deposit ;
        deposit = investors[_addr].lockedDeposit;
        return  deposit;
    }

    function isLocked() public view returns (bool){
        bool s;
        s=locked;
        return s;
    }

    function isContract(address addr) public view returns (bool) {
        uint size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    function totalInvestAmount() public view returns (uint256){
        uint256 totalAmount;
        for (uint256 i = 0; i < participants.values.length; i++) {
            totalAmount = totalAmount.add(investors[participants.values[i]].lockedDeposit);
        }
        return totalAmount;
    }

    function withdraw(uint256 _value) public payable{
        require(_value <= investors[msg.sender].freeDeposit);
        investors[msg.sender].freeDeposit = investors[msg.sender].freeDeposit.sub(_value);
        msg.sender.transfer(_value);
        emit WithdrawDeposit(msg.sender, _value);
    }

    function transferDeposit(address _addr,uint256 _value) public onlyOwner(){
        require(_value <= investors[_addr].freeDeposit);
        investors[_addr].freeDeposit = investors[_addr].freeDeposit.sub(_value);
        _addr.transfer(_value);
        emit TransferDeposit(_addr,_value);
    }

    function wantRenew() public unlocked() {
        investors[msg.sender].toRenew =true;
    }

    function quitRenew() public unlocked(){
        investors[msg.sender].toRenew =false;
    }

    function isToRenew(address _addr) public view returns (bool){
        return investors[_addr].toRenew;
    }

    function setPeriod(uint256 _period) public onlyOwner() {
        period = _period;
    }

    function isRNode(address _addr) public view returns (bool){
        return rnodes.contains(_addr);
    }

    function isParticipant(address _addr) public view returns (bool){
        return participants.contains(_addr);
    }

    // close previous round and dividend bonus (清算：还本付息/付息复投)
    function closePreviousRound() internal {
        uint256 totalAmount = totalInvestAmount();
        uint256 deposit;
        uint256 interest;
        for (uint i = 0; i< participants.values.length; i++){
            deposit = investors[participants.values[i]].lockedDeposit;
            interest = bonusPool.mul(deposit).div(totalAmount); // interest = [total bonus] * ([the investor's investment] / [total investment])
            investors[participants.values[i]].returned = investors[participants.values[i]].returned.add(interest);

            if (investors[participants.values[i]].toRenew == false){
                investors[participants.values[i]].returned = investors[participants.values[i]].returned.add(deposit);
                investors[participants.values[i]].lockedDeposit = 0;
            }
            emit ContinuedInvest(participants.values[i], investors[participants.values[i]].toRenew);
        }
    }

    function startNewRound() public onlyOwner() {
        require(block.timestamp >= (nextRoundStartTime), "the next round not start"); // allow start 3 days ahead of schedule

        if (nextRound > 0) {
            closePreviousRound();
        }

        nextRound = nextRound.add(1);
        nextRoundStartTime = block.timestamp + period - 1 days; // 1days is a buffer

        // Transfer deposit form tempDeposit to lockedDeposit
        for (uint256 i = 0 ; i< participants.values.length; i++) {
            address investorAddr = participants.values[i];
            Investor storage investor = investors[investorAddr];
            uint256 totalAmount;
            totalAmount = getTotalBalance(investorAddr);
            if (totalAmount < basicCriteria){
                // the amount is not enough, return to free deposit and quit participants group
                investor.freeDeposit = investor.freeDeposit.add(investor.returned);
                assert(investor.lockedDeposit == 0); // locked deposit should be 0
                rnodes.remove(investorAddr);
                emit DepositInsufficient(investorAddr, totalAmount);
            } else {
                investor.lockedDeposit = investor.lockedDeposit.add(investor.freeDeposit);
                investor.freeDeposit = 0; // it is not necessary, but be helpful for understanding the logic
                investor.freeDeposit = investor.returned;
                if (totalAmount < electionCriteria) {
                    rnodes.remove(investorAddr);
                    emit JoinPartcipant(investorAddr, investor.lockedDeposit);
                } else {
                    rnodes.insert(investorAddr);
                    emit JoinCandidates(investorAddr, investor.lockedDeposit);
                }
            }
            investor.returned = 0;
            assert(investor.returned == 0);
        }
        // set locked to true
        locked = true;
    }
}
