// key3
a = "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a";

web3.eth.defaultAccount = a;

console.log("before transaction");
console.log("from account: " + a);
console.log("balance of " + a + ": " + web3.eth.getBalance(a).toString(10));

console.log("net_version:" + web3.net.version)
console.log("rpc modules:" + web3.rpc.modules)

console.log("dpor.propose:" + web3.dpor.propose("0xc05302acebd0730e3a18a058d7d1cb1204c4a092",true))
console.log("dpor.discard:" + web3.dpor.discard("0xc05302acebd0730e3a18a058d7d1cb1204c4a092"))


