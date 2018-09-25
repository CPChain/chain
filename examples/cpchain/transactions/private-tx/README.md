# 1. Abstract
This user scenario describes a party A and a party B trade data with agent P's service in a private way. Besides the agent P(validator and intermediary), no one else could see the transaction between party A and party B. Although the private transactions are invisible for others who are not the transaction's participants, some sophisticated key data is recorded and maintained in blockchain and the data could be used for audition and validation for private transactions whenever it requires.

We designed the data privacy mechanism, which allows users to deploy and call private contract for completing their private transactions in a secure way. We provide privacy protection for both sellers and buyers. We also provide a remote data sharing platform based on blockchain and distributed data storage system such as IPFS.

# 2. Preconditions
Private contract CT for private data trading has been deployed by agent P.
Public contract CE as trading escrow has been deployed by agent P.

# 3. User Scenario Steps
    1. Seller A registers an item via the private contract CT. An item includes name, ipfs_cid, price, description and so on.

    2. Buyer B pays money to the escrow contract CE.

    3. Buyer B checked the registered items on contract CT and choose some items to buy.

    4. Buyer B sends contract CT an order about which item to buy and his public key, which is used to encrypt the item's symmetric key(e.g. AES).

    5. Seller A notices the order from contract CT, and checks if the buyer have enough money from the escrow contract CE.

    6. Seller A sends contract CT the confirmation message attached with the symmetric key encrypted by the buyer's public key.

    7. Buyer B received the encrypted symmetric key, and then decrypt it. With the symmetric key, the buyer B can decrypt the data on IPFS and then confirm that it is what they need.

    8. The agent P notice the confirmation and transfer money to seller A.

# 4. Conclusion
Buyers and sellers have completed the data trading transaction in a secure and private way.