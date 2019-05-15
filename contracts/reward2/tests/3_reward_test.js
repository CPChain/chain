const Reward = artifacts.require("Reward");

require('chai')
    .use(require('chai-as-promised'))
    .should();

contract("Reward with two rounds", accounts => {
    var reward;

    before(function () {
        return Reward.deployed()
            .then(inst => {
                reward = inst;
            })
            .then(async () => {
                await reward.newRaise();
                await reward.setPeriod(0);

                await reward.submitDeposit({from: accounts[1], value: web3.utils.toWei('20000', 'ether')});
                await reward.submitDeposit({from: accounts[2], value: web3.utils.toWei('21000', 'ether')});
                await reward.submitDeposit({from: accounts[3], value: web3.utils.toWei('200000', 'ether')});
                await reward.submitDeposit({from: accounts[4], value: web3.utils.toWei('210000', 'ether')});
                await reward.submitDeposit({from: accounts[5], value: web3.utils.toWei('18000', 'ether')});

                await reward.startNewRound({from:accounts[0]});

                // enter next raise period
                await reward.newRaise();
                // account2 and account3 is set to continue investment
                await reward.quitContinue({from:accounts[1]});
                await reward.wantContinue({from:accounts[2]});
                await reward.wantContinue({from:accounts[3]});
                await reward.quitContinue({from:accounts[4]});
                await reward.submitDeposit({from:accounts[2], value:web3.utils.toWei('2000', 'ether')});

                // account 4 want to get previous investment back but invest new money
                await reward.submitDeposit({from:accounts[4], value:web3.utils.toWei('100000', 'ether')})

                await reward.startNewRound({from:accounts[0]});
            })
            .then(() => {
                return reward.nextRound();
            })
            .then((round) => {
                console.log('the current round is ' + (round-1));
            });
    });

    it("it should return capital and interest to account1 and account 4", async () => {
        var total = new web3.utils.BN(web3.utils.toWei(20000+21000+200000+210000+'', 'ether'));
        var pool = new web3.utils.BN(web3.utils.toWei(1250000+'', 'ether'));
        var i1 = (new web3.utils.BN(web3.utils.toWei('20000', 'ether'))).mul(pool).div(total); // interest of account1
        var i4 = (new web3.utils.BN(web3.utils.toWei('210000', 'ether'))).mul(pool).div(total); // interest of account4

        assert.equal((await reward.getFreeBalance(accounts[1])).toString(), (new web3.utils.BN(web3.utils.toWei('20000', 'ether'))).add(i1).toString(), "account1 should be refund");
        assert.equal((await reward.getFreeBalance(accounts[4])).toString(), (new web3.utils.BN(web3.utils.toWei('210000', 'ether'))).add(i4).toString(), "account4 should be refund");       

        assert.equal((await reward.getLockedBalance(accounts[1])).toString(), '0', "account1 don't have locked balance");
        assert.equal((await reward.getLockedBalance(accounts[4])).toString(), (new web3.utils.BN(web3.utils.toWei('100000', 'ether'))).toString(), "account4 have new investment but old investment has been pay back");
    });

    it("it should only return interest, the investment is kept in the next round", async () => {
        var total = new web3.utils.BN(web3.utils.toWei(20000+21000+200000+210000+'', 'ether'));
        var pool = new web3.utils.BN(web3.utils.toWei(1250000+'', 'ether'));
        var i2 = (new web3.utils.BN(web3.utils.toWei('21000', 'ether'))).mul(pool).div(total); // interest of account1
        var i3 = (new web3.utils.BN(web3.utils.toWei('200000', 'ether'))).mul(pool).div(total); // interest of account4

        // only interest
        assert.equal((await reward.getFreeBalance(accounts[2])).toString(), i2.toString(), "account2 should be paid only interest");
        assert.equal((await reward.getFreeBalance(accounts[3])).toString(), i3.toString(), "account3 should be paid only interest");

        assert.equal((await reward.getLockedBalance(accounts[2])).toString(), web3.utils.toWei(21000+2000+'', 'ether'), "account2 continues the investment");
        assert.equal((await reward.getLockedBalance(accounts[3])).toString(), web3.utils.toWei('200000', 'ether'), "account3 continues the investment");
    });
})