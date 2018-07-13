a = "0xed9d02e382b34818e88b88a309c7fe71e65f419d";
b = "0xca843569e3427144cead5e4d5999a3d0ccf92b8e";

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

