# Reward Smart Contract 

As described in [Basic Rewards](../preliminaries/overview.md#basic-rewards), each
season is divided into three parts: raising (3 days), lock-up (84 days),
and settlement (3 days).

## API

There are several APIs in reward contract which are further divided into
two classes **admin** and **investor** according to the authority.

Here we list all APIs below.

### Admin API

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="2">                             Admin                               </th>
	</tr>
	<tr>
		<th colspan="1"> API                              </th>
		<th colspan="1">           Description        </th>
	</tr>
	<tr>
		<td  rowspan="1"> <code>newRaise()</code> </td>
		<td  rowspan="1"> Inaugurate a new raising period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>newLock()</code> </td>
		<td  rowspan="1"> Inaugurate a new lock-up period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>newSettlement()</code> </td>
		<td  rowspan="1"> Inaugurate a new settlement period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>distributeInterest(address investor)</code> </td>
		<td  rowspan="1"> Distribute interest for a user. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setRaisePeriod(uint256 _raisePeriod)</code> </td>
		<td  rowspan="1"> Set the length for raising period. The default value is 3 days. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setLockPeriod(uint256 _lockPeriod)</code> </td>
		<td  rowspan="1"> Set the length for lock-up period. The default value is 84 days. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setSettlementPeriod(uint256 _settlementPeriod)</code> </td>
		<td  rowspan="1"> Set the length for settlement period. The default value is 3 days. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setEnodeThreshold(uint256 _enodeThreshold)</code> </td>
		<td  rowspan="1"> Set the threshold to become an economy node. The default value is 20,000 tokens. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setNextRaiseTime(uint256 _NextRaiseTime)</code> </td>
		<td  rowspan="3"> Set the the time to inaugurate the next period. Normally, it is automatically calculated. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setNextLockTime(uint256 _NextLockTime)</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>setNextSettlementTime(uint256 _NextSettlementTime)</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>refund(address investor, uint 256 amount)</code> </td>
		<td  rowspan="2"> Refund the deposit in this contract to a node, and disable the contract. Both functions are invoked only when this smart contract is going to terminate. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>disable()</code> </td>
	</tr>
</table>

### Investor API

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="2">                            Investor                             </th>
	</tr>
	<tr>
		<th colspan="1"> API                              </th>
		<th colspan="1">           Description        </th>
	</tr>
	<tr>
		<td  rowspan="1"> <code>deposit()</code> </td>
		<td  rowspan="1"> It is invoked when deposit in economy pool. The value of the transaction is the amount of deposit. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>withdraw(uint amount)</code> </td>
		<td  rowspan="1"> It is invoked when withdraw deposit. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>claimInterest()</code> </td>
		<td  rowspan="1"> Investor claim interest in settlement period. </td>
	</tr>
</table>

### Read-only API

The reward contract all provides read-only API to seek information about
the node.

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="2">                             Read-only                           </th>
	</tr>
	<tr>
		<th colspan="1"> API                              </th>
		<th colspan="1">           Description        </th>
	</tr>
	<tr>
		<td  rowspan="1"> <code>mapping(address => uint 256) public investments</code> </td>
		<td  rowspan="1"> Query for the invest of an address in the pool. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>mapping(address => mapping( address => bool )) returned</code> </td>
		<td  rowspan="1"> Return a boolean result that whether an address has been distributed interest in a certain round. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public totalInvestment</code> </td>
		<td  rowspan="1"> Query for current total investment of the pool. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public totalInterest</code> </td>
		<td  rowspan="1"> Query for distributed interest of the current season. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>bool public inRaise</code> </td>
		<td  rowspan="1"> Return if it is in raising period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>bool public inLock</code> </td>
		<td  rowspan="1"> Return if it is in lock-up period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>bool public inSettlement</code> </td>
		<td  rowspan="1"> Return if it is in settlement period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public bonusPool</code> </td>
		<td  rowspan="1"> Query for the total bonus in the pool. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public round</code> </td>
		<td  rowspan="1"> Query for the sequence number of the current season.</td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public nextRaiseTime</code> </td>
		<td  rowspan="1"> Query for the beginning of the next raising period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public nextLockTime</code> </td>
		<td  rowspan="1"> Query for the beginning of the next lock-up period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>uint256 public nextSettlementTime</code> </td>
		<td  rowspan="1"> Query for the beginning of the next settlement period. </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>function getEnodes() public view returns(address[])</code> </td>
		<td  rowspan="1"> Retrieve the address of all economy nodes. </td>
	</tr>
</table>

## Availability of API

Some APIs can ony be called in a certain period. The table below lists
all available APIs for each period.

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="1"> Period                           </th>
		<th colspan="1">           API                </th>
	</tr>
	<tr>
		<td  rowspan="4"> **Raising** </td>
		<td  rowspan="1"> <code>deposit()</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>withdraw(uint amount)</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> Receive transfer. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Read-only API </td>
	</tr>
	<tr>
		<td  rowspan="1"> **Lock-up** </td>
		<td  rowspan="1"> Read-only API </td>
	</tr>
	<tr>
		<td  rowspan="3"> **Settlement** </td>
		<td  rowspan="1"> <code>claimInterest</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> <code>distributeInterest(address investor)</code> </td>
	</tr>
	<tr>
		<td  rowspan="1"> Read-only API </td>
	</tr>
</table>
