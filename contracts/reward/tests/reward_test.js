const Reward = artifacts.require("Reward")

require('chai').use(require('chai-as-promised')).should();

contract("Locked Reward", accounts => {
    it("it should reject any investment in locked status", async () => {
        var reward = await Reward.deployed();
        await reward.submitDeposit({from:accounts[1], value: 10000})
            .should.be.rejected;
        await reward.submitDeposit({from:accounts[0], value: 10000})
            .should.be.rejected;
    });

    it("it should call setBonusPool by owner and cannot be called by non-owner", async () => {
        var reward = await Reward.deployed();
        await reward.setBonusPool(web3.utils.toWei('1000000', 'ether'), {from: accounts[0]})
            .should.be.ok;;

        var bonus = await reward.bonusPool();
        assert.equal(bonus.toString(), web3.utils.toWei('1000000', 'ether'));

        await reward.setBonusPool(web3.utils.toWei('1000000', 'ether'), {from: accounts[1]})
            .should.be.rejected;

        await reward.setBonusPool(web3.utils.toWei('1000000', 'ether'), {from: accounts[2]})
            .should.be.rejected;
    });

    it("it should return true when query 'isLocked' status", () => {
        var reward
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                return reward.isLocked();
            })
            .then(isLocked => {
                assert.equal(isLocked, true, "isLocked should be true")
                return reward.isContract(accounts[0]);
            })
            .then((isContract) => {
                assert.equal(isContract, false, "account 0 should be non-contract")
            })
    });

    it("it should return false for 'isLocked' after new raise", () => {
        return Reward.deployed()
          .then(inst => {
            reward = inst;
            reward.newRaise();
            return reward
          })
          .then((reward) => {
            return reward.isLocked();
          })
          .then(isLocked => {
            assert.equal(isLocked, false, "isLocked should be false")
          });
    });
});

contract("Reward begining the first raise", accounts => {
    beforeEach(function() {
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.newRaise();
            });
    });

    it('it should return 19000 cpc for free balance and 0 cpc for locked balance after deposit 19000 cpc', () => {
        var reward;
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.submitDeposit({value: 19000, from: accounts[0]});
            })
            .then(() => {
                return reward.getFreeBalance(accounts[0]);
            })
            .then((b) => {
                assert.equal(b, 19000, "the free balance should be 19000")
            })
            .then(() => {
                return reward.getLockedBalance(accounts[0]);
            })
            .then((b) => {
                assert.equal(b, 0, "the locked balance should be 0")
            })
            .then(() => {
                return reward.nextRound()
            })
            .then((round) => {
                assert.equal(round, 0, "next round should be 0")
            });
    });

    it('it should return 19000 cpc for free balance and 0 cpc for locked balance after start new round, and next round should be 1', () => {
        var reward;
        return Reward.deployed()
            .then(inst => {
                reward = inst;
                reward.submitDeposit({value: 19000, from: accounts[1]});
            })
            .then(() => {
                reward.startNewRound({from: accounts[0]});
            })
            .then(() => {
                console.log(reward.getFreeBalance(accounts[1]), ", ", reward.getLockedBalance(accounts[1]))
                return reward.getFreeBalance(accounts[1]);
            })
            .then((b) => {
                assert.equal(b, 19000, "the free balance should be 19000")
            })
            .then(() => {
                return reward.getLockedBalance(accounts[1]);
            })
            .then((b) => {
                assert.equal(b, 0, "the locked balance should be 0")
            })
            .then(() => {
                return reward.nextRound()
            })
            .then((round) => {
                assert.equal(round, 1, "next round should be 1")
            });
    });

    it('it should only allow owner to start a new round', async () => {
        var reward = await Reward.deployed();
        await reward.startNewRound({from: accounts[2]})
            .should.be.rejected;

        await reward.startNewRound({from: accounts[0]})
            .should.be.ok;
    });
});

