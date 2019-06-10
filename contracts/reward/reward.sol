/**
 * reward contract is for participants to deposit money and gain revenue
**/


pragma solidity ^0.4.24;

import "./lib/safeMath.sol";
import "./lib/set.sol";

contract Reward {
    using Set for Set.Data;
    using SafeMath for uint256;

    address owner;
    bool public locked = true; // indicate status of the contract, if true, nobody can deposit
    uint256 public basicCriteria = 20000 ether;
    uint256 public bonusPool = 0 ether; // 1.25m x 4 = 5m (cpc)
    uint256 public nextRound = 0;
    Set.Data internal participants; // enodes
    uint256 public nextRoundStartTime = 0;
    uint256 public period = 90 days;

    // This is a type for a single investor
    struct Investor {
        uint256 freeDeposit; // amount that can be taken out
        uint256 lockedDeposit; // locked amount
        uint256 returned; // amount that will be returned to investor after a round
        bool toRenew; // if true, the person will continue to invest
    }

    // store a 'Investor' struct for each possible address
    mapping (address => Investor) public investors;

    // These events will be emitted on changes
    event OwnerSetBonusPool(uint value);
    event SubmitDeposit(address who,uint256 value);
    event WithdrawDeposit(address who, uint256 value);
    event JoinEnodes(address who, uint256 value);
    event RefundDeposit(address who, uint256 value);
    event NewRaise(uint256 round, bool lock,uint256 _bonusPool);
    event DepositInsufficient(address who,uint256 value);
    event ContinuedInvest(address _addr,bool _iscontinue);
    event FundBonusPool(uint256 value);
    event RefundAll(uint256 num);

    modifier onlyOwner() {require(msg.sender == owner);_;}

    // have to unlock the contract before starting a new raise
    modifier unlocked() {
        require(locked == false);
        _;
    }

    constructor () public {
        owner = msg.sender;
    }

    // value transferred to contract without calling any legitimate function will fund the bonus pool
    function () public payable {
        bonusPool = bonusPool.add(msg.value);
        emit FundBonusPool(msg.value);
    }

    // owner start a new raise by unlocking the contract
    function newRaise() public onlyOwner {
        locked = false;
        emit NewRaise(nextRound,locked,bonusPool);
    }

    // if the contract is abandoned, owner can refund all and lock the contract
    function disableContract() public onlyOwner {
        newRaise();
        for(uint256 i=0; i<participants.values.length; i++){
            investors[participants.values[i]].toRenew = false;
        }
        nextRoundStartTime = 1; // a very small number
        startNewRound();
        locked = true;
    }

    // owner set amount of bonus pool by transferring money to contract
    function setBonusPool() public payable onlyOwner {
        bonusPool = bonusPool.add(msg.value);
        emit OwnerSetBonusPool(bonusPool);
    }

    // deposit money to become a participate after the contract being unlocked
    // investors will be added into participants after submitting deposit
    // the amount will not locked until new round start
    function submitDeposit() public payable unlocked {
        require(!isContract(msg.sender),"please not use contract call this function");
        require(msg.sender>0);
        if (!isEnode(msg.sender)){
            participants.insert(msg.sender);
        }
        investors[msg.sender].freeDeposit = investors[msg.sender].freeDeposit.add(msg.value);
        emit SubmitDeposit(msg.sender,msg.value);
    }

    // get investor's total balance: freeDeposit + lockedDeposit
    function getTotalBalanceOf(address _addr) public view returns (uint256){
        uint256 freeBalance=0;
        uint256 lockedBalance=0;
        freeBalance = investors[_addr].freeDeposit;
        lockedBalance = investors[_addr].lockedDeposit;
        return freeBalance.add(lockedBalance);
    }

    function getFreeBalanceOf(address _addr) public view returns (uint256){
        uint256  deposit;
        deposit = investors[_addr].freeDeposit;
        return  deposit;
    }

    function getLockedBalanceOf(address _addr) public view returns (uint256){
        uint256  deposit ;
        deposit = investors[_addr].lockedDeposit;
        return  deposit;
    }

    // judge whether an address is contract address by checking extcodesize
    function isContract(address addr) public view returns (bool) {
        uint size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    // go through all participants and accumulate locked amount
    // participants.value is a list that stores all participant addresses
    // 'participants' is a new defined type set.Data. see lib/set.sol
    function getTotalLockedAmount() public view returns (uint256) {
        uint256 totalAmount = 0;
        for (uint256 i = 0; i < participants.values.length; i++) {
            totalAmount = totalAmount.add(investors[participants.values[i]].lockedDeposit);
        }
        return totalAmount;
    }

    // go through all participants and accumulate total amount: locked + free
    function getTotalAmount()public view returns (uint256) {
        uint256 totalAmount = 0;
        for (uint256 i = 0; i < participants.values.length; i++){
            totalAmount = totalAmount.add(getTotalBalanceOf(participants.values[i]));
        }
        return totalAmount;
    }

    // investors withdraw their free deposit
    function withdraw(uint256 _value) public {
        require(_value <= investors[msg.sender].freeDeposit);
        investors[msg.sender].freeDeposit = investors[msg.sender].freeDeposit.sub(_value);
        msg.sender.transfer(_value);
        emit WithdrawDeposit(msg.sender, _value);
    }

    // owner can transfer investors' free deposit to their address
    function refundDeposit(address _addr,uint256 _value) public onlyOwner {
        require(_value <= investors[_addr].freeDeposit);
        investors[_addr].freeDeposit = investors[_addr].freeDeposit.sub(_value);
        _addr.transfer(_value);
        emit RefundDeposit(_addr,_value);
    }

    function refundAll() public onlyOwner {
        uint256 num = participants.values.length;
        for(uint256 i=0; i<num; i++){
            refundDeposit(participants.values[i], investors[participants.values[i]].freeDeposit);
        }
        emit RefundAll(num);
    }

    function wantRenew() public unlocked {
        investors[msg.sender].toRenew =true;
    }

    function quitRenew() public unlocked {
        investors[msg.sender].toRenew =false;
    }

    function isToRenew(address _addr) public view returns (bool){
        return investors[_addr].toRenew;
    }

    // this function is for special situation
    // usually owner will not set this parameter directly
    function setNextRoundStartTime(uint time) public onlyOwner {
        nextRoundStartTime = time;
    }

    function setPeriod(uint256 _period) public onlyOwner {
        period = _period;

    }

    function setCriteria(uint256 criteria) public onlyOwner {
        basicCriteria = criteria;
    }

    function isEnode(address _addr) public view returns (bool){
        return participants.contains(_addr);
    }

    // close previous round and dividend bonus
    function closePreviousRound() internal {
        uint256 totalAmount = getTotalLockedAmount(); // total amount of locked money
        if (totalAmount == 0) {  // no investors
            return;
        }

        uint256 deposit;
        uint256 interest;

        // go through participants, get locked deposit and calculate interest for each
        // interest will be added to returned amount
        // if participant does not renew, locked deposit will also be added to returned amount
        // participants will renew by default
        for (uint i = 0; i< participants.values.length; i++){
            deposit = investors[participants.values[i]].lockedDeposit;
            interest = bonusPool.mul(deposit).div(totalAmount); // interest = [total bonus] * ([the investor's investment] / [total investment])
            bonusPool = bonusPool.sub(interest);
            investors[participants.values[i]].returned = investors[participants.values[i]].returned.add(interest);

            if (investors[participants.values[i]].toRenew == false){
                investors[participants.values[i]].returned = investors[participants.values[i]].returned.add(deposit);
                investors[participants.values[i]].lockedDeposit = 0;
            }
            emit ContinuedInvest(participants.values[i], investors[participants.values[i]].toRenew);
        }
    }

    // delete participants whose total balance is 0
    function cleanParticipants() internal {
        uint256 currentSize = participants.values.length;
        for(uint i=0; i<currentSize; i++) {
            address investorAddress = participants.values[i];
            uint256 totalBalance;
            totalBalance = getTotalBalanceOf(investorAddress);
            if(totalBalance == 0) {
                participants.remove(investorAddress);
            }
        }
    }

    // only owner can start a new round
    function startNewRound() public onlyOwner {
        require(block.timestamp >= (nextRoundStartTime), "the next round not start"); // allow start 3 days ahead of schedule

        // close previous round firstly
        if (nextRound > 0) {
            closePreviousRound();
        }

        // next round
        nextRound = nextRound.add(1);
        nextRoundStartTime = block.timestamp + period - 1 days; // 1days is a buffer

        // Transfer deposit form freeDeposit to lockedDeposit
        for (uint256 i = 0 ; i< participants.values.length; i++) {
            address investorAddr = participants.values[i];
            // keyword storage indicates a reference
            Investor storage investor = investors[investorAddr];
            uint256 totalAmount;
            totalAmount = getTotalBalanceOf(investorAddr);
            if (totalAmount < basicCriteria){
                // the amount is not enough, return to free deposit and quit participants group
                investor.freeDeposit = investor.freeDeposit.add(investor.returned);
                assert(investor.lockedDeposit == 0); // locked deposit should be 0
                emit DepositInsufficient(investorAddr, totalAmount);
            } else {
                investor.lockedDeposit = investor.lockedDeposit.add(investor.freeDeposit);
                investor.freeDeposit = 0; // it is not necessary, but be helpful for understanding the logic
                investor.freeDeposit = investor.returned;
                investor.toRenew = true;  // by default it is "to renew" in each round
            }
            investor.returned = 0;
        }
        // set locked to true
        locked = true;
        cleanParticipants();
    }

    function getInvestors() public view returns (address[]) {
        return participants.getAll();
    }
}

