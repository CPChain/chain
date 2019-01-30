const Reward = artifacts.require("Reward");

require('chai')
    .use(require('chai-as-promised'))
    .should();

var ether = Math.pow(10, 18);

contract("Reward with investors at initial stage", accounts => {
    before(function () {
        var reward;
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.newRaise();
            })
            .then(async () => {
                await reward.submitDeposit({from: accounts[1], value: web3.utils.toWei('20000', 'ether')});
                await reward.submitDeposit({from: accounts[2], value: web3.utils.toWei('21000', 'ether')});
                await reward.submitDeposit({from: accounts[3], value: web3.utils.toWei('200000', 'ether')});
                await reward.submitDeposit({from: accounts[4], value: web3.utils.toWei('210000', 'ether')});
                await reward.submitDeposit({from: accounts[5], value: web3.utils.toWei('18000', 'ether')});
            })
            .then(() => {
                return reward.nextRound()
            })
            .then((round) => {
                assert.equal(round, 0, "nextRound should be 0");
            });
    });

    it("it should return correct free deposit and locked deposit", async () => {
        var reward = await Reward.deployed();
        assert.equal(await reward.getFreeBalance(accounts[1]), web3.utils.toWei('20000', 'ether'));
        assert.equal(await reward.getFreeBalance(accounts[2]), web3.utils.toWei('21000', 'ether'));
        assert.equal(await reward.getFreeBalance(accounts[3]), web3.utils.toWei('200000', 'ether'));
        assert.equal(await reward.getFreeBalance(accounts[4]), web3.utils.toWei('210000', 'ether'));
        assert.equal(await reward.getFreeBalance(accounts[5]), web3.utils.toWei('18000', 'ether'));

        assert.equal(await reward.getLockedBalance(accounts[1]), 0);
        assert.equal(await reward.getLockedBalance(accounts[2]), 0);
        assert.equal(await reward.getLockedBalance(accounts[3]), 0);
        assert.equal(await reward.getLockedBalance(accounts[4]), 0);
        assert.equal(await reward.getLockedBalance(accounts[5]), 0);        
    });

    it("it should return decrease investment balance after withdraw and transfer", async () => {
        var reward = await Reward.deployed();
        var balance = await web3.eth.getBalance(accounts[1]);

        reward.withdraw(web3.utils.toWei('1000', 'ether'), {from:accounts[1]});
        var remain = await reward.getFreeBalance(accounts[1]);
        assert.equal(remain, web3.utils.toWei('19000', 'ether'), "should remain 19000");

        var afterBalance = await web3.eth.getBalance(accounts[1]);
        assert.equal(Math.round((afterBalance-balance)/ether, 3), 1000.000, "withdraw 1000");

        balance = await web3.eth.getBalance(accounts[1]);
        reward.transferDeposit(accounts[1], web3.utils.toWei('2000', 'ether'));
        remain = await reward.getFreeBalance(accounts[1]);
        assert.equal(remain, web3.utils.toWei('17000', 'ether'), "should remain 17000");

        afterBalance = await web3.eth.getBalance(accounts[1]);
        assert.equal(Math.round((afterBalance - balance)/ether, 3), 2000.000);

        contractBalance = await web3.eth.getBalance(reward.address);
        assert.equal(Math.round(contractBalance/ether, 3), 20000+21000+200000+210000+18000-2000-1000);
    });

    it("the total investment should be 0", () => {
        var reward;
        return Reward.deployed()
            .then((inst) => {
                reward = inst;
            })
            .then(() => {
                return reward.totalInvestAmount();
            })
            .then((amount) => {
                assert.equal(amount.toNumber(), 0, "total investment amount is wrong");
            });
    });

    it("it should be able to start new round", async () => {
        var reward = await Reward.deployed();
        await reward.startNewRound({from:accounts[0]});
    });
});

contract("Reward with investors at locked stage", accounts => {
    var reward;

    before(function () {
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.newRaise();
            })
            .then(async () => {
                await reward.submitDeposit({from: accounts[1], value: web3.utils.toWei('20000', 'ether')});
                await reward.submitDeposit({from: accounts[2], value: web3.utils.toWei('21000', 'ether')});
                await reward.submitDeposit({from: accounts[3], value: web3.utils.toWei('200000', 'ether')});
                await reward.submitDeposit({from: accounts[4], value: web3.utils.toWei('210000', 'ether')});
                await reward.submitDeposit({from: accounts[5], value: web3.utils.toWei('18000', 'ether')});
            })
            .then(() => {
                return reward.startNewRound({from:accounts[0]});
            })
            .then(() => {
                return reward.nextRound();
            })
            .then((round) => {
                console.log('the current round is ' + (round-1));
            });
    });

    it("it should return correct 'isContinue'", async () => {
        await reward.newRaise();
        await reward.wantContinue({from: accounts[1]});
        await reward.quitContinue({from: accounts[2]});

        var c = await reward.isContinue(accounts[1]);
        assert.equal(c, true);
        c = await reward.isContinue(accounts[2]);
        assert.equal(c, false);
        c = await reward.isContinue(accounts[3]);
        assert.equal(c, false);
    });

    it("the total investment should be correct", async () => {
        var b = await reward.totalInvestAmount();
        assert.equal(b.toString(), web3.utils.toWei(20000+21000+200000+210000+'', 'ether'));
    });

    it('candidates should contain account3 and account4, not contain account1 and account2', async () => {
        var isP1 = await reward.isParticipant(accounts[1]);
        var isP2 = await reward.isParticipant(accounts[2]);
        var isP3 = await reward.isParticipant(accounts[3]);
        var isP4 = await reward.isParticipant(accounts[4]);
        var isP5 = await reward.isParticipant(accounts[5]);

        var isC1 = await reward.isCandidate(accounts[1]);
        var isC2 = await reward.isCandidate(accounts[2]);
        var isC3 = await reward.isCandidate(accounts[3]);
        var isC4 = await reward.isCandidate(accounts[4]);
        var isC5 = await reward.isCandidate(accounts[5]);

        assert.equal(isP1, true, "account1 should be participant");
        assert.equal(isP2, true, "account2 should be participant");
        assert.equal(isP3, true, "account3 should be participant");
        assert.equal(isP4, true, "account4 should be participant");
        assert.equal(isP5, true, "account5 should be participant, although the amount is not enough");

        assert.equal(isC1, false, "account1 should not be candidate");
        assert.equal(isC2, false, "account2 should not be candidate");
        assert.equal(isC3, true, "account3 should be candidate");
        assert.equal(isC4, true, "account4 should be candidate");
        assert.equal(isC5, false, "account4 should not be candidate");
    });

    it('should reject start next round before the time point is reached', async () => {
        var reward = await Reward.deployed();
        await reward.startNewRound()
            .should.be.rejectedWith('the next round not start');
    });
});

contract("Reward when first round finished", accounts => {
    var reward;

    before(function () {
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.newRaise();
            })
            .then(async () => {
                await reward.submitDeposit({from: accounts[1], value: web3.utils.toWei('20000', 'ether')});
                await reward.submitDeposit({from: accounts[2], value: web3.utils.toWei('21000', 'ether')});
                await reward.submitDeposit({from: accounts[3], value: web3.utils.toWei('200000', 'ether')});
                await reward.submitDeposit({from: accounts[4], value: web3.utils.toWei('210000', 'ether')});
                await reward.submitDeposit({from: accounts[5], value: web3.utils.toWei('18000', 'ether')});
            })
            .then(() => {
                return reward.setPeriod(0);
            })
            .then(() => {
                return reward.startNewRound({from:accounts[0]});
            })
            .then(() => {
                return reward.send(web3.utils.toWei('1250000', 'ether'));
            })
            .then(() => {
                // enter next round, close the first round
                return reward.startNewRound({from:accounts[0]});
            })
            .then(() => {
                return reward.nextRound();
            })
            .then((round) => {
                console.log('the current round is ' + (round-1));
            });
    });

    it("it should returns 2 for next round", async () => {
        var c = await reward.nextRound();
        assert.equal(c.toNumber(), 2);
    });

    it("it should return interest for investors", async () => {
        var total = new web3.utils.BN(web3.utils.toWei(20000+21000+200000+210000+'', 'ether'));
        var pool = new web3.utils.BN(web3.utils.toWei(1250000+'', 'ether'));
        var b1 = await reward.getFreeBalance(accounts[1]);
        var b2 = await reward.getFreeBalance(accounts[2]);
        var b3 = await reward.getFreeBalance(accounts[3]);
        var b4 = await reward.getFreeBalance(accounts[4]);

        console.log("investor1 got interest: " + b1.div(new web3.utils.BN(ether+'')).toString());
        console.log("investor2 got interest: " + b2.div(new web3.utils.BN(ether+'')).toString());
        console.log("investor3 got interest: " + b3.div(new web3.utils.BN(ether+'')).toString());
        console.log("investor4 got interest: " + b4.div(new web3.utils.BN(ether+'')).toString());

        assert.equal(b1.toString(), (new web3.utils.BN(web3.utils.toWei('20000', 'ether'))).mul(pool).div(total).toString(), "investor 1's interest is wrong");
        assert.equal(b2.toString(), (new web3.utils.BN(web3.utils.toWei('21000', 'ether'))).mul(pool).div(total).toString(), "investor 2's interest is wrong");
        assert.equal(b3.toString(), (new web3.utils.BN(web3.utils.toWei('200000', 'ether'))).mul(pool).div(total).toString(), "investor 3's interest is wrong");
        assert.equal(b4.toString(), (new web3.utils.BN(web3.utils.toWei('210000', 'ether'))).mul(pool).div(total).toString(), "investor 4's interest is wrong");
    });
})
