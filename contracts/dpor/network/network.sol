pragma solidity ^0.4.24;


contract Network {
    string public host = "www.microsoft.com:443";
    uint256 public count = 3;
    uint256 public timeout = 300;
    uint256 public gap = 100;
    bool public open = true;

    address owner;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    event UpdateConfig(string config, uint256 value);
    event UpdateHost(string value);
    event UpdateOpen(bool value);

    constructor() public {
        owner = msg.sender;
    }

    function updateHost(string _host) public onlyOwner {
        host = _host;
        emit UpdateHost(host);
    }

    function updateCount(uint256 _count) public onlyOwner {
        require(_count>=1 && _count<=20);
        count = _count;
        emit UpdateConfig("count", count);
    }

    function updateTimeout(uint256 _timeout) public onlyOwner {
        require(_timeout>=50 && _timeout<=10000);
        timeout = _timeout;
        emit UpdateConfig("timeout", timeout);
    }

    function updateGap(uint256 _gap) public onlyOwner {
        require(_gap>=10 && _gap<=3000);
        gap = _gap;
        emit UpdateConfig("gap", gap);
    }

    function updateOpen(bool _open) public onlyOwner {
        open = _open;
        emit UpdateOpen(open);
    }
}