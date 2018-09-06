
// addresses
a = "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a";
b = "0xc05302acebd0730e3a18a058d7d1cb1204c4a092";
c = "0xEF3dd127DE235F15ffB4FC0D71469d1339DF6465";

// new contract
var CampaignContract = web3.eth.contract([{"constant":true,"inputs":[],"name":"minimumNoc","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"view_idx","type":"uint256"}],"name":"CandidatesOf","outputs":[{"name":"","type":"address[]"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"candidate","type":"address"}],"name":"CandidateInfoOf","outputs":[{"name":"","type":"uint256"},{"name":"","type":"uint256"},{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"baseDeposit","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"maximumNoc","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"viewIdx","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"ViewChange","outputs":[],"payable":true,"stateMutability":"payable","type":"function"},{"constant":true,"inputs":[],"name":"minimumRpt","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"num_of_campaign","type":"uint256"},{"name":"rpt","type":"uint256"}],"name":"ClaimCampaign","outputs":[],"payable":true,"stateMutability":"payable","type":"function"},{"constant":false,"inputs":[],"name":"QuitCampaign","outputs":[],"payable":true,"stateMutability":"payable","type":"function"},{"inputs":[],"payable":false,"stateMutability":"nonpayable","type":"constructor"}]);

// load contract
var Campaign = CampaignContract.at("0x1a9fAE75908752d0ABf4DCa45ebcaC311C376290");

console.log("Campaign status: ")

// console.log("owner: " + Campaign.owner)
console.log("base deposit: " + Campaign.baseDeposit().toString());
console.log("minimum rpt: " + Campaign.minimumRpt().toString());
console.log("minimum noc: " + Campaign.minimumNoc().toString());
console.log("maximum noc: " + Campaign.maximumNoc().toString());
console.log("view index: " + Campaign.viewIdx().toString())

console.log("Candidates status: ")

console.log("candidates: 0: " + Campaign.CandidatesOf(0));
console.log("candidates: 1: " + Campaign.CandidatesOf(1));
console.log("candidates: viewIdx: " +  Campaign.viewIdx().toString() + ": "+ Campaign.CandidatesOf(Campaign.viewIdx()));

console.log("candidate info of:" + a + ": "+ Campaign.CandidateInfoOf(a));
console.log("candidate info of:" + b + ": "+ Campaign.CandidateInfoOf(b));
