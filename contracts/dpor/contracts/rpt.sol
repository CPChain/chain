pragma solidity ^0.4.24;

/** @title Reputation calculate */

contract RPT {
    /** The 5 weight configs. */
    uint public alpha = 1;
    uint public beta = 1;
    uint public gamma = 1;
    uint public psi = 1;
    uint public omega = 1;
    
    /** other configs.*/
    uint public window = 4;
    uint public f = 21;
    
    address public owner;
    
    /** The 5 factors calculation expressions. */
    //getBalance() is a go function.
    string public coinAge = "alpha * getBalance(_addr, _blockNumber)";
    //getBaseData() means how many data someone upload in a certain block.
    //getBaseDataAmount() means the amount uploaded data by everyone in a certain block.
    string public dataContribute = "bata * (getBaseData(_addr, _blockNumber) / getDataAmount(_blockNumber) * 10 + getAddtionalData(_addr, _blockNumber) / getAddtionalDataAmount(_blockNumber) * 10)";
    string public proxyReward = "gamma * getProxyNum(_addr, _blockNumber) * proxyReward";
    string public blockchainMaintenanceRecord = "psi * fl(_addr, _blockNumber)";
    string public txAmount = "omega * fixedTxReward * txAmount";
    
    modifier onlyOwner() {require(msg.sender == owner);_;}
    
    /** logs when owner changed cpnfigs or expr. */
    event UpdateConfigs(uint blockNumber);
    event UpdateOneConfig(uint blockNumber, string configName, uint configValue);
    event SetExp(uint blockNumber, string exprNmae, string expr);

    
    
    constructor() public {
        owner = msg.sender;
    }
    
    /** modified all configs. */
    function updateConfigs(
        uint _alpha, 
        uint _beta, 
        uint _gamma, 
        uint _psi, 
        uint _omega, 
        uint _f, 
        uint _window
        ) 
        public 
        onlyOwner()
        {
            alpha = _alpha;
            beta = _beta;
            gamma = _gamma;
            psi = _psi;
            omega = _omega;
            window = _window;
            f = _f;
            
            emit UpdateConfigs(block.number);
        }
    
    /** modified one config. */
    function updateAlpha(uint _alpha) public onlyOwner(){
        alpha = _alpha;
        emit UpdateOneConfig(block.number, "alpha", alpha);
    }
    
    function updateBeta(uint _beta) public onlyOwner() {
        beta = _beta;
        emit UpdateOneConfig(block.number, "beta", beta);
    }
    
    function updateGamma(uint _gamma) public onlyOwner() {
        gamma = _gamma;
        emit UpdateOneConfig(block.number, "gamma", gamma);
    }
    
    function updatePsi(uint _psi) public onlyOwner() {
        psi = _psi;
        emit UpdateOneConfig(block.number, "psi", psi);
    }
    
    function updateOmega(uint _omega) public onlyOwner() {
        omega = _omega;
        emit UpdateOneConfig(block.number, "omega", omega);
    }
    
    function updateWindow(uint _window) public onlyOwner() {
        window = _window;
        emit UpdateOneConfig(block.number, "window", window);
    }
    
    // function rpt(address _addr, uint _blocknumber) public returns(uint) {
    //     uint i = 0;
    //     uint rpt = 0;
    //     uint blocknumber = _blocknumber;
    //     for(i=0; i<window;i++){
    //         rpt += alpha * (getBalance(blocknumber, _addr));
    //         rpt += beta * (getBasicContribution(blocknumber, _addr) + getAdditionalContribution(blocknumber, _addr));
    //         rpt += gamma * (getProxyAward(blocknumber, _addr));
    //         rpt += psi * (isCommitee(blocknumber, _addr));
    //         rpt += omega * (getTxAward(blocknumber, _addr));
    //         blocknumber--;
    //     }
    //     return rpt;
    // }
    
    
    /** set expressions. */
    function setCoinAgeExp(string _coinAge) public onlyOwner() returns(string) {
        coinAge = _coinAge;
        emit  SetExp(block.number, "coinAge", coinAge);
        return coinAge;
    }
    
    function setDataContributeExp(string _dataContribute) public onlyOwner() returns(string) {
        dataContribute = _dataContribute;
        emit  SetExp(block.number, "dataContribute", dataContribute);
        return dataContribute;
    }
    
    function setProxyRewardExp(string _proxyReward) public onlyOwner() returns(string) {
        proxyReward = _proxyReward;
        emit  SetExp(block.number, "proxyReward", proxyReward);
        return proxyReward;
    }
    
    function setBlockchainMaintenanceRecordExp(string _blockchainMaintenanceRecord) public onlyOwner() returns(string) {
        blockchainMaintenanceRecord = _blockchainMaintenanceRecord;
        emit  SetExp(block.number, "blockchainMaintenanceRecord", blockchainMaintenanceRecord);
        return blockchainMaintenanceRecord;
    }
    
    function setTxAmountExp(string _txAmount) public onlyOwner() returns(string) {
        txAmount = _txAmount;
        emit  SetExp(block.number, "txAmount", txAmount);
        return txAmount;
    }
}





