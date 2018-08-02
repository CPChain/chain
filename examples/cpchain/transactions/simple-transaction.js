// key3
a = "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a";
// key4
b = "0xc05302acebd0730e3a18a058d7d1cb1204c4a092";

web3.eth.defaultAccount = a;

console.log("before transaction");
console.log("from account: " + a);
console.log("balance of " + a + ": " + web3.eth.getBalance(a).toString(10));
console.log("to account: " + b);
console.log("balance of " + b + "is " + web3.eth.getBalance(b).toString(10));


simpleTx = {
    to: b,
    value: 1000000000000000000
};

web3.eth.sendTransaction(simpleTx, function(err, transactionHash) {
    if(!err) {
        console.log("transaction completed");
        console.log(transactionHash);
        console.log("balance of " + a + ": " + web3.eth.getBalance(a).toString(10));
        console.log("balance of " + b + ": " + web3.eth.getBalance(b).toString(10));
    }
});

