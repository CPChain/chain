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
| Term                      | A term refers a period that a batch|
|                           | of proposers elected for a certain |
|                           | proposers committee. Term is a     |
|                           | monotone increasing integer, whose |
|                           | value is added by one each time    |
|                           | it changes                         |
+---------------------------+------------------------------------+
| Epoch                     | An obsolete variable name for      |
|                           | *term*                             |
|                           |                                    |
+---------------------------+------------------------------------+
| TermLen                   | Short for term length. It refers to|
|                           | the number of proposers in a       |
|                           | certain term. This value limits    |
|                           | the size of proposers committee,   |
|                           | and remains a constant unless the  |
|                           | consensus model adjusts            |
+---------------------------+------------------------------------+
| View                      | It represents the index of the     |
|                           | proposer in the committee in a     |
|                           | certain term. This value is an     |
|                           | integer varying from 1 to TermLen  |
|                           |                                    |
|                           |                                    |
+---------------------------+------------------------------------+
| Round                     | An obsolete variable name for      |
|                           | *view*                             |
|                           |                                    |
+---------------------------+------------------------------------+
| ViewLen                   | A proposer is able to propose one  |
|                           | or more blocks when it comes to its|
|                           | view. The number of blocks it can  |
|                           | propose is ViewLen. It is also     |
|                           | fixed unless the consensus model   |
|                           | adjusts                            |
+---------------------------+------------------------------------+
