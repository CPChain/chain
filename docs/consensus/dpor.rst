dpor
******

+------------+------------+
|PBFT        | Blockchain |
+============+============+
| primary    | leader     |
+------------+------------+
| backup     | signer     |
+------------+------------+
| replica    |            |
+------------+------------+
|            |            |
+------------+------------+

- **Normal Case**
    - **Pre-prepare**
        - The *leader* p broadcasts a <<PRE−PREPARE, v, n, d>,m>
        - v: the view
        - n: sequence number
        - d: digest of message
        - m: message
    - **Prepare**
        - A *signer* i enters prepare phase after it accepts a PRE-PREPARE message for this view
        - i multicasts a <PREPARE, v, n, d, i> to all replicas
        - i adds PRE-PREPARE and PREPARE messages into the log
        - i is collecting *prepare certificate*
            - Prepare certificate is 2f+1 PREPARE messages (including i) matching with the PRE-PREPARE message in terms of v, d and n
    - **Commit**
        - i is *prepared* if it collects the prepare certificate, and enters commit phase
        - i multicasts a <COMMIT, v, n, d, i> message to all replicas
        - i adds COMMIT message into the log
        - i is collecting *commit certificate*
            - Commit certificate is 2f+1 COMMIT messages (including i) matching with each other with the same v, d and n
    - **Reply**
        - After i collects a commit certificate, it executes the request
        - i add the block into its log
- **View Change**
    - In view i
        - Once the timer of a signer i expires, i multicasts a empty block with a VIEW-CHANGE message into the network
        - The VIEW-CHANGE message is <VIEW − CHANGE, v+1 ,n ,i>
        - The primary p of view v+1 is collecting view-change certificate
            - View-change certificate is 2f+1 VIEW-CHANGE messages (including p)
    - Entering new view i+1
        - After p collects VIEW-CHANGE certificate, it multicast a <NEW-VIEW, v+1> message
        - Signer i enters new view v+1