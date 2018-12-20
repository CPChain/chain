Glossary
~~~~~~~~~~

+---------------------------+------------------------------------+
| Term                      |           Description              |
+===========================+====================================+
| Validators Committee      | A group of users that can validate |
|                           | a newly proposed block             |
+---------------------------+------------------------------------+
| Validator                 | A member of validators committee   |
+---------------------------+------------------------------------+
| Proposers Committee       | A group of users elected for a     |
|                           | certain term that can propose      |
|                           | blocks                             |
+---------------------------+------------------------------------+
| Proposer                  | A member of proposers committee    |
|                           | that can can proposes a new block  |
|                           | in this view                       |
+---------------------------+------------------------------------+
| Civilian                  | All users except the proposer and  |
|                           | validators from the committee      |
+---------------------------+------------------------------------+
| Seal                      | A unforgeable signature indicating |
|                           | the proposer of corresponding      |
|                           | for a certain block number         |
+---------------------------+------------------------------------+
| Sigs                      | An array of unforgeable signatures |
|                           | the proposer of corresponding      |
|                           | for a certain block number         |
+---------------------------+------------------------------------+
| P-Certificate             | A validator has a P-certificate    |
|                           | if it has 2f+1 PREPARE messages    |
|                           | for a certain block number         |
+---------------------------+------------------------------------+
| C-Certificate             | A validator has a C-certificate    |
|                           | if it has 2f+1 COMMIT messages     |
|                           | for a certain block number         |
+---------------------------+------------------------------------+
| Impeachment               | If a validator suspects the propo  |
|                           | ser is faulty or non-responding,   |
|                           | it activate an impeachment process |
+---------------------------+------------------------------------+
| Impeachment block         | In an impeachment, a validator is  |
|                           | aiming to propose an impeach block |
|                           | on behalf of the a faulty proposer |
+---------------------------+------------------------------------+