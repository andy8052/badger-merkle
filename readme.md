## Usage
To generate the snapshot data:

```
pip install -r requirements.txt

brownie networks add Ethereum archive host=$YOUR_ARCHIVE_NODE chainid=1

rm -rf snapshot
brownie run snapshot --network archive
```

To validate the snapshot with an end-to-end test distribution:

```
brownie run distribution
```

To deploy the distributor on the mainnet:

```
brownie run snapshot deploy --network mainnet
```