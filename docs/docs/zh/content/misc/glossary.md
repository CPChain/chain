# Glossary

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="1"> Term                      </th>
		<th colspan="1">           Description              </th>
	</tr>
	<tr>
		<td  rowspan="1"> DPoR </td>
		<td  rowspan="1"> Short for *Dynamic Proof of* *Reputation*. It is the consensus algorithm among proposers. </td>
	</tr>
	<tr>
		<td  rowspan="1"> LBFT </td>
		<td  rowspan="1"> Short for *Lightweight Byzantine* *Fault Tolerance*. It is a consensus algorithm inspired by PBFT. </td>
	</tr>
	<tr>
		<td  rowspan="1"> LBFT 2.0 </td>
		<td  rowspan="1"> An improved version of LBFT. It is the current consensus algorithm among validators. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Validators Committee </td>
		<td  rowspan="1"> A group of users that can validate a newly proposed block. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Validator </td>
		<td  rowspan="1"> A member of validators committee. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Proposers Committee </td>
		<td  rowspan="1"> A group of users elected for a certain term that can propose blocks. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Proposer </td>
		<td  rowspan="1"> A member of proposers committee that can can proposes a new block in this view. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Civilian </td>
		<td  rowspan="1"> All users except the proposer and validators from the committee. </td>
	</tr>
	<tr>
		<td  rowspan="1"> RNode </td>
		<td  rowspan="1"> Short for *reputation node*. By depositing 200k tokens in reputation pool, a node can become an RNode. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Economy node </td>
		<td  rowspan="1"> By depositing 20k tokens in economy node, a node can become an economy node. Sometimes it is abbreviated into *ENode*. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Industry node </td>
		<td  rowspan="1"> The node held CPChain partners. It can also propose blocks like other RNodes. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Seal </td>
		<td  rowspan="1"> A unforgeable signature indicating the proposer of corresponding for a certain block number. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Sigs </td>
		<td  rowspan="1"> An array of unforgeable signatures the proposer of corresponding for a certain block number. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Quorum </td>
		<td  rowspan="1"> A quorum refers to a subset of committee members that can represent the whole committee to proceed to next state. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Strong Quorum </td>
		<td  rowspan="1"> A quorum of 2f+1 members. It is used in normal cases. Unless otherwise specified, *quorum* is always referring to strong quorum. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Weak Quorum </td>
		<td  rowspan="1"> A quorum of f+1 members. It is only used in impeach cases. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Certificate </td>
		<td  rowspan="1"> a validator has a certificate if it is a member of a quorum. holding a certificate indicates it can enter the next state </td>
	</tr>
	<tr>
		<td  rowspan="1"> Strong Certificate </td>
		<td  rowspan="1"> The certificate obtained by a strong quorum. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Weak Certificate </td>
		<td  rowspan="1"> The certificate obtained by a weak quorum. </td>
	</tr>
	<tr>
		<td  rowspan="1"> P-Certificate </td>
		<td  rowspan="1"> A validator has a P-certificate if it has 2f+1 PREPARE messages or f+1 impeach PREPARE messages for a certain block number. </td>
	</tr>
	<tr>
		<td  rowspan="1"> C-Certificate </td>
		<td  rowspan="1"> A validator has a C-certificate if it has 2f+1 COMMIT messages or f+1 impeach COMMIT messages for a certain block number. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Impeachment </td>
		<td  rowspan="1"> If a validator suspects the propo ser is faulty or non-responding, it activate an impeachment process.</td>
	</tr>
	<tr>
		<td  rowspan="1"> Impeachment block </td>
		<td  rowspan="1"> In an impeachment, a validator is aiming to propose an impeach block on behalf of the a faulty proposer.</td>
	</tr>
	<tr>
		<td  rowspan="1"> Term </td>
		<td  rowspan="1"> A term refers a period that a batch of proposers elected for a certain proposers committee. Term is a monotone increasing integer, whose value is added by one each time it changes. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Epoch </td>
		<td  rowspan="1"> An obsolete variable name for *term*. </td>
	</tr>
	<tr>
		<td  rowspan="1"> TermLen </td>
		<td  rowspan="1"> Short for term length. It refers to the number of proposers in a certain term. This value limits the size of proposers committee, and remains a constant unless the consensus model adjusts. </td>
	</tr>
	<tr>
		<td  rowspan="1"> View </td>
		<td  rowspan="1"> Available values of *view* are 0,1, and 2. It represents the sequence number of the block sealed by any proposer. Each view contains 12 blocks and their corresponding proposers. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Round </td>
		<td  rowspan="1"> An obsolete variable name for *view*. </td>
	</tr>
	<tr>
		<td  rowspan="1"> ViewLen </td>
		<td  rowspan="1"> A proposer is able to propose one or more blocks when it comes to its view. The number of blocks it can propose is ViewLen. It is also fixed unless the consensus model adjusts. </td>
	</tr>
	<tr>
		<td  rowspan="1"> Period </td>
		<td  rowspan="1"> Minimum time interval between two consecutive blocks. The value is set to 10 seconds. </td>
	</tr>
</table>
