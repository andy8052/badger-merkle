import json
import os
import math
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from functools import partial, wraps
from itertools import zip_longest
from pathlib import Path

import toml
from brownie import MerkleDistributor, Wei, accounts, interface, rpc, web3
from eth_abi import decode_single, encode_single
from eth_abi.packed import encode_abi_packed
from eth_utils import encode_hex
from toolz import valfilter, valmap
from tqdm import tqdm, trange
from click import secho

TIPPER_AMOUNT = Wei('10000 ether')
YGOV_AMOUNT = Wei('140000 ether')
DISTRIBUTOR_ADDRESS = '0x5e37996bcfF8C169e77b00D7b6e7261bbC60761e'
START_BLOCK = 10553531
SNAPSHOT_BLOCK = 11146722

cwbtcAddress = '0xC11b1268C1A384e55C48c2391d8d480264A3A7F4'
aaveLendAddress = '0x3dfd23A6c5E8BbcFc9581d2E864a68feb6a076d3'
metaAddress = '0x0372f3696fA7dC99801F435FD6737E57818239F2'
uniWBTCETHAddress = '0xBb2b8038a1640196FbE3e38816F3e67Cba72D940'
awbtcAddress = '0xFC4B8ED459e00e5400be803A9BB3954234FD50e3'
wbtcBalAddress = '0x1efF8aF5D577060BA4ac8A29A13525bb0Ee2A3D5'
wbtcAddress = '0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599'
sbtcLPAddress = '0x075b1bb99792c9E1041bA13afEf80C91a1e70fB3'
renbtcLPAddress = '0x49849C98ae39Fff122806C06791Fa73784FB3675'
wbtcMinters = ["0xa726c00CDa1f60AaaB19BC095D02A46556837f31", "0x0967AeA99754974a4CC4DBf29009155A49588171", "0x808E4981f6287B13711b78DE9d7C169E5D180643", "0x9bA1014bD2E50f4Fb601Ca178416e76ACa8d2810", "0xA2b1A32CC725d32936E0E81f79F0D41C44cc5cFA", "0xd5c01B2f8Ab1e00B84fae74a354f57448F68D882", "0x572F17EcfFf768F9C31881F66BD97B18a651fc20", "0xFDF28Bf25779ED4cA74e958d54653260af604C20", "0x658545e34E392FE07177e1794504838B49eD261D", "0x3854DD5E2657D18e686707c2b652928f6F6AAA51", "0xFAF0708D1aEd2566205D61f471d7e4Aeb10910Ea", "0xB43D7a63391BC768D5981b0D91152eb76DEE9a6A", "0xDa520bdaB7b196446099413f27d0fA77F72d9799", "0xbec897d7e4969C59993bfE9ad7b4c571a29Aa381", "0x14C436e9a41A3e8CD365621FAB43B57bba7A39C8", "0x1520dd2Ccb0c150e5716f57a77c703D95427acbC", "0xe1F3C653248De6894d683cB2f10DE7CA2253046f", "0xaCF9e2469fBc57E6Ad391f97a41f8Aad4d68B097", "0x03dC1CCc9559Fb309b56275BE427EBCff0d1766f", "0x8E63Bb7Af326de3fc6e09F4c8D54A75c6e236abA"]
sbtcAddress = '0xe4b679400F0f267212D5D812B95f58C83243EE71'
tbtcAddress = '0x8dAEBADE922dF735c38C80C7eBD708Af50815fAa'
renbtcAddress = '0xEB4C2781e4ebA804CE9a9803C67d0893436bB27D'
joinwbtcAddress = '0xBF72Da2Bd84c5170618Fbe5914B0ECA9638d5eb5'
ygovAddress = '0xBa37B002AbaFDd8E89a1995dA52740bbC013D992'
DAI = interface.ERC20('0x6B175474E89094C44Da98b954EedeAC495271d0F')
UNISWAP_FACTORY = '0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f'
ZERO_ADDRESS = '0x0000000000000000000000000000000000000000'

merkleABI = r'''[{"inputs":[{"internalType":"address","name":"token_","type":"address"},{"internalType":"bytes32","name":"merkleRoot_","type":"bytes32"}],"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":false,"internalType":"uint256","name":"index","type":"uint256"},{"indexed":false,"internalType":"address","name":"account","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount","type":"uint256"}],"name":"Claimed","type":"event"},{"inputs":[{"internalType":"uint256","name":"index","type":"uint256"},{"internalType":"address","name":"account","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"},{"internalType":"bytes32[]","name":"merkleProof","type":"bytes32[]"},{"internalType":"uint256","name":"tipBips","type":"uint256"}],"name":"claim","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_token","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"collectDust","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"uint256","name":"index","type":"uint256"}],"name":"isClaimed","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"merkleRoot","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"token","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"}]'''
merkleABI = json.loads(merkleABI)
wbtcABI = r'''[{"constant":true,"inputs":[],"name":"mintingFinished","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"_spender","type":"address"},{"name":"_value","type":"uint256"}],"name":"approve","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"_token","type":"address"}],"name":"reclaimToken","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"_from","type":"address"},{"name":"_to","type":"address"},{"name":"_value","type":"uint256"}],"name":"transferFrom","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"unpause","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"_to","type":"address"},{"name":"_amount","type":"uint256"}],"name":"mint","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"value","type":"uint256"}],"name":"burn","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"claimOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"paused","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"_spender","type":"address"},{"name":"_subtractedValue","type":"uint256"}],"name":"decreaseApproval","outputs":[{"name":"success","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"name":"_owner","type":"address"}],"name":"balanceOf","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"renounceOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"finishMinting","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"pause","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"owner","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"_to","type":"address"},{"name":"_value","type":"uint256"}],"name":"transfer","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"_spender","type":"address"},{"name":"_addedValue","type":"uint256"}],"name":"increaseApproval","outputs":[{"name":"success","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"name":"_owner","type":"address"},{"name":"_spender","type":"address"}],"name":"allowance","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"pendingOwner","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"newOwner","type":"address"}],"name":"transferOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"anonymous":false,"inputs":[],"name":"Pause","type":"event"},{"anonymous":false,"inputs":[],"name":"Unpause","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"burner","type":"address"},{"indexed":false,"name":"value","type":"uint256"}],"name":"Burn","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"to","type":"address"},{"indexed":false,"name":"amount","type":"uint256"}],"name":"Mint","type":"event"},{"anonymous":false,"inputs":[],"name":"MintFinished","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"previousOwner","type":"address"}],"name":"OwnershipRenounced","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"previousOwner","type":"address"},{"indexed":true,"name":"newOwner","type":"address"}],"name":"OwnershipTransferred","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"owner","type":"address"},{"indexed":true,"name":"spender","type":"address"},{"indexed":false,"name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"from","type":"address"},{"indexed":true,"name":"to","type":"address"},{"indexed":false,"name":"value","type":"uint256"}],"name":"Transfer","type":"event"}]'''
wbtcABI = json.loads(wbtcABI)
renbtcABI = r'''[{"anonymous":false,"inputs":[{"indexed":false,"internalType":"bytes","name":"_to","type":"bytes"},{"indexed":false,"internalType":"uint256","name":"_amount","type":"uint256"},{"indexed":true,"internalType":"uint256","name":"_n","type":"uint256"},{"indexed":true,"internalType":"bytes","name":"_indexedTo","type":"bytes"}],"name":"LogBurn","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_to","type":"address"},{"indexed":false,"internalType":"uint256","name":"_amount","type":"uint256"},{"indexed":true,"internalType":"uint256","name":"_n","type":"uint256"},{"indexed":true,"internalType":"bytes32","name":"_signedMessageHash","type":"bytes32"}],"name":"LogMint","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_newMintAuthority","type":"address"}],"name":"LogMintAuthorityUpdated","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"previousOwner","type":"address"},{"indexed":true,"internalType":"address","name":"newOwner","type":"address"}],"name":"OwnershipTransferred","type":"event"},{"constant":false,"inputs":[{"internalType":"address","name":"_token","type":"address"}],"name":"blacklistRecoverableToken","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"bytes","name":"_to","type":"bytes"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"burn","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"burnFee","outputs":[{"internalType":"uint16","name":"","type":"uint16"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"claimOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"claimTokenOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"feeRecipient","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"bytes32","name":"_pHash","type":"bytes32"},{"internalType":"uint256","name":"_amount","type":"uint256"},{"internalType":"address","name":"_to","type":"address"},{"internalType":"bytes32","name":"_nHash","type":"bytes32"}],"name":"hashForSignature","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"contract RenERC20LogicV1","name":"_token","type":"address"},{"internalType":"address","name":"_feeRecipient","type":"address"},{"internalType":"address","name":"_mintAuthority","type":"address"},{"internalType":"uint16","name":"_mintFee","type":"uint16"},{"internalType":"uint16","name":"_burnFee","type":"uint16"},{"internalType":"uint256","name":"_minimumBurnAmount","type":"uint256"}],"name":"initialize","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_nextOwner","type":"address"}],"name":"initialize","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"isOwner","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"minimumBurnAmount","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"bytes32","name":"_pHash","type":"bytes32"},{"internalType":"uint256","name":"_amountUnderlying","type":"uint256"},{"internalType":"bytes32","name":"_nHash","type":"bytes32"},{"internalType":"bytes","name":"_sig","type":"bytes"}],"name":"mint","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"mintAuthority","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"mintFee","outputs":[{"internalType":"uint16","name":"","type":"uint16"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"nextN","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"owner","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"pendingOwner","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_token","type":"address"}],"name":"recoverTokens","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"renounceOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"name":"status","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"token","outputs":[{"internalType":"contract RenERC20LogicV1","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"newOwner","type":"address"}],"name":"transferOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"contract GatewayLogicV1","name":"_nextTokenOwner","type":"address"}],"name":"transferTokenOwnership","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint16","name":"_nextBurnFee","type":"uint16"}],"name":"updateBurnFee","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_nextFeeRecipient","type":"address"}],"name":"updateFeeRecipient","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"_minimumBurnAmount","type":"uint256"}],"name":"updateMinimumBurnAmount","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_nextMintAuthority","type":"address"}],"name":"updateMintAuthority","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint16","name":"_nextMintFee","type":"uint16"}],"name":"updateMintFee","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"bytes32","name":"_signedMessageHash","type":"bytes32"},{"internalType":"bytes","name":"_sig","type":"bytes"}],"name":"verifySignature","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"}]'''
renbtcABI = json.loads(renbtcABI)
cwbtcABI = r'''[{"constant":true,"inputs":[],"name":"name","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"spender","type":"address"},{"name":"amount","type":"uint256"}],"name":"approve","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"repayAmount","type":"uint256"}],"name":"repayBorrow","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"reserveFactorMantissa","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"account","type":"address"}],"name":"borrowBalanceCurrent","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"exchangeRateStored","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"src","type":"address"},{"name":"dst","type":"address"},{"name":"amount","type":"uint256"}],"name":"transferFrom","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"borrower","type":"address"},{"name":"repayAmount","type":"uint256"}],"name":"repayBorrowBehalf","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"pendingAdmin","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"owner","type":"address"}],"name":"balanceOfUnderlying","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"getCash","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"newComptroller","type":"address"}],"name":"_setComptroller","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"totalBorrows","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"comptroller","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"reduceAmount","type":"uint256"}],"name":"_reduceReserves","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"initialExchangeRateMantissa","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"accrualBlockNumber","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"underlying","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"owner","type":"address"}],"name":"balanceOf","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"totalBorrowsCurrent","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"redeemAmount","type":"uint256"}],"name":"redeemUnderlying","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"totalReserves","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"account","type":"address"}],"name":"borrowBalanceStored","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"mintAmount","type":"uint256"}],"name":"mint","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"accrueInterest","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"dst","type":"address"},{"name":"amount","type":"uint256"}],"name":"transfer","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"borrowIndex","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"supplyRatePerBlock","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"liquidator","type":"address"},{"name":"borrower","type":"address"},{"name":"seizeTokens","type":"uint256"}],"name":"seize","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"newPendingAdmin","type":"address"}],"name":"_setPendingAdmin","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"exchangeRateCurrent","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"name":"account","type":"address"}],"name":"getAccountSnapshot","outputs":[{"name":"","type":"uint256"},{"name":"","type":"uint256"},{"name":"","type":"uint256"},{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"borrowAmount","type":"uint256"}],"name":"borrow","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"redeemTokens","type":"uint256"}],"name":"redeem","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"name":"owner","type":"address"},{"name":"spender","type":"address"}],"name":"allowance","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"_acceptAdmin","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"newInterestRateModel","type":"address"}],"name":"_setInterestRateModel","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"interestRateModel","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"borrower","type":"address"},{"name":"repayAmount","type":"uint256"},{"name":"cTokenCollateral","type":"address"}],"name":"liquidateBorrow","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"admin","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"borrowRatePerBlock","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"newReserveFactorMantissa","type":"uint256"}],"name":"_setReserveFactor","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"isCToken","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"inputs":[{"name":"underlying_","type":"address"},{"name":"comptroller_","type":"address"},{"name":"interestRateModel_","type":"address"},{"name":"initialExchangeRateMantissa_","type":"uint256"},{"name":"name_","type":"string"},{"name":"symbol_","type":"string"},{"name":"decimals_","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":false,"name":"interestAccumulated","type":"uint256"},{"indexed":false,"name":"borrowIndex","type":"uint256"},{"indexed":false,"name":"totalBorrows","type":"uint256"}],"name":"AccrueInterest","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"minter","type":"address"},{"indexed":false,"name":"mintAmount","type":"uint256"},{"indexed":false,"name":"mintTokens","type":"uint256"}],"name":"Mint","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"redeemer","type":"address"},{"indexed":false,"name":"redeemAmount","type":"uint256"},{"indexed":false,"name":"redeemTokens","type":"uint256"}],"name":"Redeem","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"borrower","type":"address"},{"indexed":false,"name":"borrowAmount","type":"uint256"},{"indexed":false,"name":"accountBorrows","type":"uint256"},{"indexed":false,"name":"totalBorrows","type":"uint256"}],"name":"Borrow","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"payer","type":"address"},{"indexed":false,"name":"borrower","type":"address"},{"indexed":false,"name":"repayAmount","type":"uint256"},{"indexed":false,"name":"accountBorrows","type":"uint256"},{"indexed":false,"name":"totalBorrows","type":"uint256"}],"name":"RepayBorrow","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"liquidator","type":"address"},{"indexed":false,"name":"borrower","type":"address"},{"indexed":false,"name":"repayAmount","type":"uint256"},{"indexed":false,"name":"cTokenCollateral","type":"address"},{"indexed":false,"name":"seizeTokens","type":"uint256"}],"name":"LiquidateBorrow","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"oldPendingAdmin","type":"address"},{"indexed":false,"name":"newPendingAdmin","type":"address"}],"name":"NewPendingAdmin","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"oldAdmin","type":"address"},{"indexed":false,"name":"newAdmin","type":"address"}],"name":"NewAdmin","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"oldComptroller","type":"address"},{"indexed":false,"name":"newComptroller","type":"address"}],"name":"NewComptroller","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"oldInterestRateModel","type":"address"},{"indexed":false,"name":"newInterestRateModel","type":"address"}],"name":"NewMarketInterestRateModel","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"oldReserveFactorMantissa","type":"uint256"},{"indexed":false,"name":"newReserveFactorMantissa","type":"uint256"}],"name":"NewReserveFactor","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"admin","type":"address"},{"indexed":false,"name":"reduceAmount","type":"uint256"},{"indexed":false,"name":"newTotalReserves","type":"uint256"}],"name":"ReservesReduced","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"name":"error","type":"uint256"},{"indexed":false,"name":"info","type":"uint256"},{"indexed":false,"name":"detail","type":"uint256"}],"name":"Failure","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"from","type":"address"},{"indexed":true,"name":"to","type":"address"},{"indexed":false,"name":"amount","type":"uint256"}],"name":"Transfer","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"owner","type":"address"},{"indexed":true,"name":"spender","type":"address"},{"indexed":false,"name":"amount","type":"uint256"}],"name":"Approval","type":"event"}]'''
wbtcjoinABI = r'''[{"inputs":[{"internalType":"address","name":"vat_","type":"address"},{"internalType":"bytes32","name":"ilk_","type":"bytes32"},{"internalType":"address","name":"gem_","type":"address"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":true,"inputs":[{"indexed":true,"internalType":"bytes4","name":"sig","type":"bytes4"},{"indexed":true,"internalType":"address","name":"usr","type":"address"},{"indexed":true,"internalType":"bytes32","name":"arg1","type":"bytes32"},{"indexed":true,"internalType":"bytes32","name":"arg2","type":"bytes32"},{"indexed":false,"internalType":"bytes","name":"data","type":"bytes"}],"name":"LogNote","type":"event"},{"constant":false,"inputs":[],"name":"cage","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"dec","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"usr","type":"address"}],"name":"deny","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"guy","type":"address"},{"internalType":"uint256","name":"wad","type":"uint256"}],"name":"exit","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"gem","outputs":[{"internalType":"contract GemLike5","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"ilk","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"urn","type":"address"},{"internalType":"uint256","name":"wad","type":"uint256"}],"name":"join","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"live","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"usr","type":"address"}],"name":"rely","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"vat","outputs":[{"internalType":"contract VatLike","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"wards","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"}]'''
proxyABI = r'''[{"constant":false,"inputs":[{"name":"owner_","type":"address"}],"name":"setOwner","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"_target","type":"address"},{"name":"_data","type":"bytes"}],"name":"execute","outputs":[{"name":"response","type":"bytes32"}],"payable":true,"stateMutability":"payable","type":"function"},{"constant":false,"inputs":[{"name":"_code","type":"bytes"},{"name":"_data","type":"bytes"}],"name":"execute","outputs":[{"name":"target","type":"address"},{"name":"response","type":"bytes32"}],"payable":true,"stateMutability":"payable","type":"function"},{"constant":true,"inputs":[],"name":"cache","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"authority_","type":"address"}],"name":"setAuthority","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"owner","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"_cacheAddr","type":"address"}],"name":"setCache","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"authority","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"inputs":[{"name":"_cacheAddr","type":"address"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"payable":true,"stateMutability":"payable","type":"fallback"},{"anonymous":true,"inputs":[{"indexed":true,"name":"sig","type":"bytes4"},{"indexed":true,"name":"guy","type":"address"},{"indexed":true,"name":"foo","type":"bytes32"},{"indexed":true,"name":"bar","type":"bytes32"},{"indexed":false,"name":"wad","type":"uint256"},{"indexed":false,"name":"fax","type":"bytes"}],"name":"LogNote","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"authority","type":"address"}],"name":"LogSetAuthority","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"owner","type":"address"}],"name":"LogSetOwner","type":"event"}]'''
awbtcABI = r'''[{"inputs":[{"internalType":"contract LendingPoolAddressesProvider","name":"_addressesProvider","type":"address"},{"internalType":"address","name":"_underlyingAsset","type":"address"},{"internalType":"uint8","name":"_underlyingAssetDecimals","type":"uint8"},{"internalType":"string","name":"_name","type":"string"},{"internalType":"string","name":"_symbol","type":"string"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"owner","type":"address"},{"indexed":true,"internalType":"address","name":"spender","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":true,"internalType":"address","name":"_to","type":"address"},{"indexed":false,"internalType":"uint256","name":"_value","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_toBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromIndex","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_toIndex","type":"uint256"}],"name":"BalanceTransfer","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":false,"internalType":"uint256","name":"_value","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromIndex","type":"uint256"}],"name":"BurnOnLiquidation","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":true,"internalType":"address","name":"_to","type":"address"}],"name":"InterestRedirectionAllowanceChanged","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":true,"internalType":"address","name":"_to","type":"address"},{"indexed":false,"internalType":"uint256","name":"_redirectedBalance","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromIndex","type":"uint256"}],"name":"InterestStreamRedirected","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":false,"internalType":"uint256","name":"_value","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromIndex","type":"uint256"}],"name":"MintOnDeposit","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_from","type":"address"},{"indexed":false,"internalType":"uint256","name":"_value","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_fromIndex","type":"uint256"}],"name":"Redeem","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"_targetAddress","type":"address"},{"indexed":false,"internalType":"uint256","name":"_targetBalanceIncrease","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_targetIndex","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_redirectedBalanceAdded","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"_redirectedBalanceRemoved","type":"uint256"}],"name":"RedirectedBalanceUpdated","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"from","type":"address"},{"indexed":true,"internalType":"address","name":"to","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Transfer","type":"event"},{"constant":true,"inputs":[],"name":"UINT_MAX_VALUE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_to","type":"address"}],"name":"allowInterestRedirectionTo","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"owner","type":"address"},{"internalType":"address","name":"spender","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_account","type":"address"},{"internalType":"uint256","name":"_value","type":"uint256"}],"name":"burnOnLiquidation","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"subtractedValue","type":"uint256"}],"name":"decreaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"}],"name":"getInterestRedirectionAddress","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"}],"name":"getRedirectedBalance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"}],"name":"getUserIndex","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"addedValue","type":"uint256"}],"name":"increaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"isTransferAllowed","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_account","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"mintOnDeposit","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"_user","type":"address"}],"name":"principalBalanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"redeem","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_to","type":"address"}],"name":"redirectInterestStream","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_from","type":"address"},{"internalType":"address","name":"_to","type":"address"}],"name":"redirectInterestStreamOf","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"sender","type":"address"},{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_from","type":"address"},{"internalType":"address","name":"_to","type":"address"},{"internalType":"uint256","name":"_value","type":"uint256"}],"name":"transferOnLiquidation","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"underlyingAssetAddress","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"}]'''
sbtcLPABI = r'''[{"name":"Transfer","inputs":[{"type":"address","name":"_from","indexed":true},{"type":"address","name":"_to","indexed":true},{"type":"uint256","name":"_value","indexed":false}],"anonymous":false,"type":"event"},{"name":"Approval","inputs":[{"type":"address","name":"_owner","indexed":true},{"type":"address","name":"_spender","indexed":true},{"type":"uint256","name":"_value","indexed":false}],"anonymous":false,"type":"event"},{"outputs":[],"inputs":[{"type":"string","name":"_name"},{"type":"string","name":"_symbol"},{"type":"uint256","name":"_decimals"},{"type":"uint256","name":"_supply"}],"constant":false,"payable":false,"type":"constructor"},{"name":"set_minter","outputs":[],"inputs":[{"type":"address","name":"_minter"}],"constant":false,"payable":false,"type":"function","gas":36247},{"name":"totalSupply","outputs":[{"type":"uint256","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":1181},{"name":"allowance","outputs":[{"type":"uint256","name":"out"}],"inputs":[{"type":"address","name":"_owner"},{"type":"address","name":"_spender"}],"constant":true,"payable":false,"type":"function","gas":1519},{"name":"transfer","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":74802},{"name":"transferFrom","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_from"},{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":111953},{"name":"approve","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_spender"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":39012},{"name":"mint","outputs":[],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":75733},{"name":"burn","outputs":[],"inputs":[{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":76623},{"name":"burnFrom","outputs":[],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":76696},{"name":"name","outputs":[{"type":"string","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":7853},{"name":"symbol","outputs":[{"type":"string","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":6906},{"name":"decimals","outputs":[{"type":"uint256","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":1511},{"name":"balanceOf","outputs":[{"type":"uint256","name":"out"}],"inputs":[{"type":"address","name":"arg0"}],"constant":true,"payable":false,"type":"function","gas":1695}]'''
renbtcLPABI = r'''[{"name":"Transfer","inputs":[{"type":"address","name":"_from","indexed":true},{"type":"address","name":"_to","indexed":true},{"type":"uint256","name":"_value","indexed":false}],"anonymous":false,"type":"event"},{"name":"Approval","inputs":[{"type":"address","name":"_owner","indexed":true},{"type":"address","name":"_spender","indexed":true},{"type":"uint256","name":"_value","indexed":false}],"anonymous":false,"type":"event"},{"outputs":[],"inputs":[{"type":"string","name":"_name"},{"type":"string","name":"_symbol"},{"type":"uint256","name":"_decimals"},{"type":"uint256","name":"_supply"}],"constant":false,"payable":false,"type":"constructor"},{"name":"set_minter","outputs":[],"inputs":[{"type":"address","name":"_minter"}],"constant":false,"payable":false,"type":"function","gas":36247},{"name":"totalSupply","outputs":[{"type":"uint256","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":1181},{"name":"allowance","outputs":[{"type":"uint256","name":"out"}],"inputs":[{"type":"address","name":"_owner"},{"type":"address","name":"_spender"}],"constant":true,"payable":false,"type":"function","gas":1519},{"name":"transfer","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":74802},{"name":"transferFrom","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_from"},{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":111953},{"name":"approve","outputs":[{"type":"bool","name":"out"}],"inputs":[{"type":"address","name":"_spender"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":39012},{"name":"mint","outputs":[],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":75733},{"name":"burn","outputs":[],"inputs":[{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":76623},{"name":"burnFrom","outputs":[],"inputs":[{"type":"address","name":"_to"},{"type":"uint256","name":"_value"}],"constant":false,"payable":false,"type":"function","gas":76696},{"name":"name","outputs":[{"type":"string","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":7853},{"name":"symbol","outputs":[{"type":"string","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":6906},{"name":"decimals","outputs":[{"type":"uint256","name":"out"}],"inputs":[],"constant":true,"payable":false,"type":"function","gas":1511},{"name":"balanceOf","outputs":[{"type":"uint256","name":"out"}],"inputs":[{"type":"address","name":"arg0"}],"constant":true,"payable":false,"type":"function","gas":1695}]'''
uniWBTCETHABI = r'''[{"inputs":[],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"owner","type":"address"},{"indexed":true,"internalType":"address","name":"spender","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1","type":"uint256"},{"indexed":true,"internalType":"address","name":"to","type":"address"}],"name":"Burn","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1","type":"uint256"}],"name":"Mint","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0In","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1In","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount0Out","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1Out","type":"uint256"},{"indexed":true,"internalType":"address","name":"to","type":"address"}],"name":"Swap","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"internalType":"uint112","name":"reserve0","type":"uint112"},{"indexed":false,"internalType":"uint112","name":"reserve1","type":"uint112"}],"name":"Sync","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"from","type":"address"},{"indexed":true,"internalType":"address","name":"to","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Transfer","type":"event"},{"constant":true,"inputs":[],"name":"DOMAIN_SEPARATOR","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MINIMUM_LIQUIDITY","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"PERMIT_TYPEHASH","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"},{"internalType":"address","name":"","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"burn","outputs":[{"internalType":"uint256","name":"amount0","type":"uint256"},{"internalType":"uint256","name":"amount1","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"factory","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getReserves","outputs":[{"internalType":"uint112","name":"_reserve0","type":"uint112"},{"internalType":"uint112","name":"_reserve1","type":"uint112"},{"internalType":"uint32","name":"_blockTimestampLast","type":"uint32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_token0","type":"address"},{"internalType":"address","name":"_token1","type":"address"}],"name":"initialize","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"kLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"mint","outputs":[{"internalType":"uint256","name":"liquidity","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"nonces","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"owner","type":"address"},{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"},{"internalType":"uint256","name":"deadline","type":"uint256"},{"internalType":"uint8","name":"v","type":"uint8"},{"internalType":"bytes32","name":"r","type":"bytes32"},{"internalType":"bytes32","name":"s","type":"bytes32"}],"name":"permit","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"price0CumulativeLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"price1CumulativeLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"skim","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"amount0Out","type":"uint256"},{"internalType":"uint256","name":"amount1Out","type":"uint256"},{"internalType":"address","name":"to","type":"address"},{"internalType":"bytes","name":"data","type":"bytes"}],"name":"swap","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"sync","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"token0","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"token1","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"from","type":"address"},{"internalType":"address","name":"to","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"}]'''
tbtcABI = r'''[{"inputs":[{"internalType":"address","name":"_VendingMachine","type":"address"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"owner","type":"address"},{"indexed":true,"internalType":"address","name":"spender","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"from","type":"address"},{"indexed":true,"internalType":"address","name":"to","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Transfer","type":"event"},{"constant":true,"inputs":[{"internalType":"address","name":"owner","type":"address"},{"internalType":"address","name":"spender","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"contract ITokenRecipient","name":"_spender","type":"address"},{"internalType":"uint256","name":"_value","type":"uint256"},{"internalType":"bytes","name":"_extraData","type":"bytes"}],"name":"approveAndCall","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"account","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"burn","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_account","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"burnFrom","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"subtractedValue","type":"uint256"}],"name":"decreaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"addedValue","type":"uint256"}],"name":"increaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_account","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"mint","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"sender","type":"address"},{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"}]'''
wbtcBalABI = r'''[{"inputs":[],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"src","type":"address"},{"indexed":true,"internalType":"address","name":"dst","type":"address"},{"indexed":false,"internalType":"uint256","name":"amt","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":true,"inputs":[{"indexed":true,"internalType":"bytes4","name":"sig","type":"bytes4"},{"indexed":true,"internalType":"address","name":"caller","type":"address"},{"indexed":false,"internalType":"bytes","name":"data","type":"bytes"}],"name":"LOG_CALL","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"caller","type":"address"},{"indexed":true,"internalType":"address","name":"tokenOut","type":"address"},{"indexed":false,"internalType":"uint256","name":"tokenAmountOut","type":"uint256"}],"name":"LOG_EXIT","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"caller","type":"address"},{"indexed":true,"internalType":"address","name":"tokenIn","type":"address"},{"indexed":false,"internalType":"uint256","name":"tokenAmountIn","type":"uint256"}],"name":"LOG_JOIN","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"caller","type":"address"},{"indexed":true,"internalType":"address","name":"tokenIn","type":"address"},{"indexed":true,"internalType":"address","name":"tokenOut","type":"address"},{"indexed":false,"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"tokenAmountOut","type":"uint256"}],"name":"LOG_SWAP","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"src","type":"address"},{"indexed":true,"internalType":"address","name":"dst","type":"address"},{"indexed":false,"internalType":"uint256","name":"amt","type":"uint256"}],"name":"Transfer","type":"event"},{"constant":true,"inputs":[],"name":"BONE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"BPOW_PRECISION","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"EXIT_FEE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"INIT_POOL_SUPPLY","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_BOUND_TOKENS","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_BPOW_BASE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_FEE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_IN_RATIO","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_OUT_RATIO","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_TOTAL_WEIGHT","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MAX_WEIGHT","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MIN_BALANCE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MIN_BOUND_TOKENS","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MIN_BPOW_BASE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MIN_FEE","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MIN_WEIGHT","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"src","type":"address"},{"internalType":"address","name":"dst","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"dst","type":"address"},{"internalType":"uint256","name":"amt","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"whom","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"token","type":"address"},{"internalType":"uint256","name":"balance","type":"uint256"},{"internalType":"uint256","name":"denorm","type":"uint256"}],"name":"bind","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceIn","type":"uint256"},{"internalType":"uint256","name":"tokenWeightIn","type":"uint256"},{"internalType":"uint256","name":"tokenBalanceOut","type":"uint256"},{"internalType":"uint256","name":"tokenWeightOut","type":"uint256"},{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcInGivenOut","outputs":[{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceIn","type":"uint256"},{"internalType":"uint256","name":"tokenWeightIn","type":"uint256"},{"internalType":"uint256","name":"tokenBalanceOut","type":"uint256"},{"internalType":"uint256","name":"tokenWeightOut","type":"uint256"},{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcOutGivenIn","outputs":[{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceOut","type":"uint256"},{"internalType":"uint256","name":"tokenWeightOut","type":"uint256"},{"internalType":"uint256","name":"poolSupply","type":"uint256"},{"internalType":"uint256","name":"totalWeight","type":"uint256"},{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcPoolInGivenSingleOut","outputs":[{"internalType":"uint256","name":"poolAmountIn","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceIn","type":"uint256"},{"internalType":"uint256","name":"tokenWeightIn","type":"uint256"},{"internalType":"uint256","name":"poolSupply","type":"uint256"},{"internalType":"uint256","name":"totalWeight","type":"uint256"},{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcPoolOutGivenSingleIn","outputs":[{"internalType":"uint256","name":"poolAmountOut","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceIn","type":"uint256"},{"internalType":"uint256","name":"tokenWeightIn","type":"uint256"},{"internalType":"uint256","name":"poolSupply","type":"uint256"},{"internalType":"uint256","name":"totalWeight","type":"uint256"},{"internalType":"uint256","name":"poolAmountOut","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcSingleInGivenPoolOut","outputs":[{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceOut","type":"uint256"},{"internalType":"uint256","name":"tokenWeightOut","type":"uint256"},{"internalType":"uint256","name":"poolSupply","type":"uint256"},{"internalType":"uint256","name":"totalWeight","type":"uint256"},{"internalType":"uint256","name":"poolAmountIn","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcSingleOutGivenPoolIn","outputs":[{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[{"internalType":"uint256","name":"tokenBalanceIn","type":"uint256"},{"internalType":"uint256","name":"tokenWeightIn","type":"uint256"},{"internalType":"uint256","name":"tokenBalanceOut","type":"uint256"},{"internalType":"uint256","name":"tokenWeightOut","type":"uint256"},{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"calcSpotPrice","outputs":[{"internalType":"uint256","name":"spotPrice","type":"uint256"}],"payable":false,"stateMutability":"pure","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"dst","type":"address"},{"internalType":"uint256","name":"amt","type":"uint256"}],"name":"decreaseApproval","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"poolAmountIn","type":"uint256"},{"internalType":"uint256[]","name":"minAmountsOut","type":"uint256[]"}],"name":"exitPool","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenOut","type":"address"},{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"},{"internalType":"uint256","name":"maxPoolAmountIn","type":"uint256"}],"name":"exitswapExternAmountOut","outputs":[{"internalType":"uint256","name":"poolAmountIn","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenOut","type":"address"},{"internalType":"uint256","name":"poolAmountIn","type":"uint256"},{"internalType":"uint256","name":"minAmountOut","type":"uint256"}],"name":"exitswapPoolAmountIn","outputs":[{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[],"name":"finalize","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"token","type":"address"}],"name":"getBalance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getColor","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getController","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getCurrentTokens","outputs":[{"internalType":"address[]","name":"tokens","type":"address[]"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"token","type":"address"}],"name":"getDenormalizedWeight","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getFinalTokens","outputs":[{"internalType":"address[]","name":"tokens","type":"address[]"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"token","type":"address"}],"name":"getNormalizedWeight","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getNumTokens","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"address","name":"tokenOut","type":"address"}],"name":"getSpotPrice","outputs":[{"internalType":"uint256","name":"spotPrice","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"address","name":"tokenOut","type":"address"}],"name":"getSpotPriceSansFee","outputs":[{"internalType":"uint256","name":"spotPrice","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getSwapFee","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getTotalDenormalizedWeight","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"token","type":"address"}],"name":"gulp","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"dst","type":"address"},{"internalType":"uint256","name":"amt","type":"uint256"}],"name":"increaseApproval","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"t","type":"address"}],"name":"isBound","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"isFinalized","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"isPublicSwap","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"poolAmountOut","type":"uint256"},{"internalType":"uint256[]","name":"maxAmountsIn","type":"uint256[]"}],"name":"joinPool","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"internalType":"uint256","name":"minPoolAmountOut","type":"uint256"}],"name":"joinswapExternAmountIn","outputs":[{"internalType":"uint256","name":"poolAmountOut","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"uint256","name":"poolAmountOut","type":"uint256"},{"internalType":"uint256","name":"maxAmountIn","type":"uint256"}],"name":"joinswapPoolAmountOut","outputs":[{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"token","type":"address"},{"internalType":"uint256","name":"balance","type":"uint256"},{"internalType":"uint256","name":"denorm","type":"uint256"}],"name":"rebind","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"manager","type":"address"}],"name":"setController","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"bool","name":"public_","type":"bool"}],"name":"setPublicSwap","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"swapFee","type":"uint256"}],"name":"setSwapFee","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"internalType":"address","name":"tokenOut","type":"address"},{"internalType":"uint256","name":"minAmountOut","type":"uint256"},{"internalType":"uint256","name":"maxPrice","type":"uint256"}],"name":"swapExactAmountIn","outputs":[{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"},{"internalType":"uint256","name":"spotPriceAfter","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"tokenIn","type":"address"},{"internalType":"uint256","name":"maxAmountIn","type":"uint256"},{"internalType":"address","name":"tokenOut","type":"address"},{"internalType":"uint256","name":"tokenAmountOut","type":"uint256"},{"internalType":"uint256","name":"maxPrice","type":"uint256"}],"name":"swapExactAmountOut","outputs":[{"internalType":"uint256","name":"tokenAmountIn","type":"uint256"},{"internalType":"uint256","name":"spotPriceAfter","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"dst","type":"address"},{"internalType":"uint256","name":"amt","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"src","type":"address"},{"internalType":"address","name":"dst","type":"address"},{"internalType":"uint256","name":"amt","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"token","type":"address"}],"name":"unbind","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"}]'''
metaABI = r'''[{"constant":true,"inputs":[],"name":"processingReward","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"memberAddress","type":"address"},{"name":"proposalIndex","type":"uint256"}],"name":"getMemberProposalVote","outputs":[{"name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getCurrentPeriod","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"","type":"address"}],"name":"members","outputs":[{"name":"delegateKey","type":"address"},{"name":"shares","type":"uint256"},{"name":"exists","type":"bool"},{"name":"highestIndexYesVote","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSharesRequested","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"newDelegateKey","type":"address"}],"name":"updateDelegateKey","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"totalShares","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"","type":"uint256"}],"name":"proposalQueue","outputs":[{"name":"proposer","type":"address"},{"name":"applicant","type":"address"},{"name":"sharesRequested","type":"uint256"},{"name":"startingPeriod","type":"uint256"},{"name":"yesVotes","type":"uint256"},{"name":"noVotes","type":"uint256"},{"name":"processed","type":"bool"},{"name":"didPass","type":"bool"},{"name":"aborted","type":"bool"},{"name":"tokenTribute","type":"uint256"},{"name":"details","type":"string"},{"name":"maxTotalSharesAtYesVote","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"","type":"address"}],"name":"memberAddressByDelegateKey","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"gracePeriodLength","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"abortWindow","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getProposalQueueLength","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"summoningTime","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"votingPeriodLength","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"sharesToBurn","type":"uint256"}],"name":"ragequit","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"proposalDeposit","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"name":"startingPeriod","type":"uint256"}],"name":"hasVotingPeriodExpired","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"applicant","type":"address"},{"name":"tokenTribute","type":"uint256"},{"name":"sharesRequested","type":"uint256"},{"name":"details","type":"string"}],"name":"submitProposal","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"proposalIndex","type":"uint256"},{"name":"uintVote","type":"uint8"}],"name":"submitVote","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"name":"highestIndexYesVote","type":"uint256"}],"name":"canRagequit","outputs":[{"name":"","type":"bool"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"guildBank","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"dilutionBound","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"periodDuration","outputs":[{"name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"approvedToken","outputs":[{"name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"name":"proposalIndex","type":"uint256"}],"name":"abort","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"name":"proposalIndex","type":"uint256"}],"name":"processProposal","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"inputs":[{"name":"summoner","type":"address"},{"name":"_approvedToken","type":"address"},{"name":"_periodDuration","type":"uint256"},{"name":"_votingPeriodLength","type":"uint256"},{"name":"_gracePeriodLength","type":"uint256"},{"name":"_abortWindow","type":"uint256"},{"name":"_proposalDeposit","type":"uint256"},{"name":"_dilutionBound","type":"uint256"},{"name":"_processingReward","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":false,"name":"proposalIndex","type":"uint256"},{"indexed":true,"name":"delegateKey","type":"address"},{"indexed":true,"name":"memberAddress","type":"address"},{"indexed":true,"name":"applicant","type":"address"},{"indexed":false,"name":"tokenTribute","type":"uint256"},{"indexed":false,"name":"sharesRequested","type":"uint256"}],"name":"SubmitProposal","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"proposalIndex","type":"uint256"},{"indexed":true,"name":"delegateKey","type":"address"},{"indexed":true,"name":"memberAddress","type":"address"},{"indexed":false,"name":"uintVote","type":"uint8"}],"name":"SubmitVote","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"proposalIndex","type":"uint256"},{"indexed":true,"name":"applicant","type":"address"},{"indexed":true,"name":"memberAddress","type":"address"},{"indexed":false,"name":"tokenTribute","type":"uint256"},{"indexed":false,"name":"sharesRequested","type":"uint256"},{"indexed":false,"name":"didPass","type":"bool"}],"name":"ProcessProposal","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"memberAddress","type":"address"},{"indexed":false,"name":"sharesToBurn","type":"uint256"}],"name":"Ragequit","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"proposalIndex","type":"uint256"},{"indexed":false,"name":"applicantAddress","type":"address"}],"name":"Abort","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"memberAddress","type":"address"},{"indexed":false,"name":"newDelegateKey","type":"address"}],"name":"UpdateDelegateKey","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"name":"summoner","type":"address"},{"indexed":false,"name":"shares","type":"uint256"}],"name":"SummonComplete","type":"event"}]'''

def cached(path):
    path = Path(path)
    codec = {'.toml': toml, '.json': json}[path.suffix]
    codec_args = {'.json': {'indent': 2}}.get(path.suffix, {})

    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            if path.exists():
                print('load from cache', path)
                return codec.loads(path.read_text())
            else:
                result = func(*args, **kwargs)
                os.makedirs(path.parent, exist_ok=True)
                path.write_text(codec.dumps(result, **codec_args))
                print('write to cache', path)
                return result

        return wrapper

    return decorator

def get_wbtc_holders():
    holders = Counter()
    contract = web3.eth.contract(wbtcAddress, abi=wbtcABI)
    for start in trange(6766284, 10486684, 1000):
        end = min(start + 999, 10486684)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            holders[log['args']['from']] -= log['args']['value']*(10486684 - log['blockNumber'])
            holders[log['args']['to']] += log['args']['value']*(10486684 - log['blockNumber'])

    filteredMints = valfilter(bool, dict(holders.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_renbtc_holders():
    holders = Counter()
    contract = web3.eth.contract(renbtcAddress, abi=wbtcABI)
    for start in trange(9736969, 10486684, 1000):
        end = min(start + 999, 10486684)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            holders[log['args']['from']] -= log['args']['value']*(10486684 - log['blockNumber'])
            holders[log['args']['to']] += log['args']['value']*(10486684 - log['blockNumber'])

    filteredMints = valfilter(bool, dict(holders.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_renbtc_mint():
    mints = Counter()
    contract = web3.eth.contract(renbtcAddress, abi=renbtcABI)
    for start in trange(9737055, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.LogMint().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            # if log['args']['from'] == ZERO_ADDRESS:
            mints[log['args']['_to']] += log['args']['_amount']

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_sbtc_mint():
    mints = Counter()
    contract = web3.eth.contract(sbtcAddress, abi=wbtcABI)
    for start in trange(8623122, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['from'] == ZERO_ADDRESS:
                mints[log['args']['to']] += log['args']['value']

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_tbtc_mint():
    mints = Counter()
    contract = web3.eth.contract(tbtcAddress, abi=tbtcABI)
    for start in trange(10867840, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['from'] == ZERO_ADDRESS:
                mints[log['args']['to']] += log['args']['value']

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_meta():
    mints = Counter()
    contract = web3.eth.contract(metaAddress, abi=metaABI)
    for start in trange(7901584, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.ProcessProposal().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            mints[log['args']['applicant']] = 1

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    return filteredMints

def get_cwbtc_mint():
    mints = Counter()
    burns  = Counter()
    contract = web3.eth.contract(cwbtcAddress, abi=cwbtcABI)
    for start in trange(8163813, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        mintLogs = contract.events.Mint().getLogs(fromBlock=start, toBlock=end)
        burnLogs = contract.events.Redeem().getLogs(fromBlock=start, toBlock=end)

        for log in mintLogs:
            mints[log['args']['minter']] += log['args']['mintAmount']*(SNAPSHOT_BLOCK - log['blockNumber'])

        for log in burnLogs:
            burns[log['args']['redeemer']] += log['args']['redeemAmount']*(SNAPSHOT_BLOCK - log['blockNumber'])

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    filteredBurns = valfilter(bool, dict(burns.most_common()))
    print(len(filteredBurns))

    final = Counter()
    for key in filteredMints:
        if key in filteredBurns:
            final[key] = filteredMints[key] - filteredBurns[key]
        else:
            final[key] = filteredMints[key]

    filteredFinal = valfilter(bool, dict(final.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_awbtc_mint():
    mints = Counter()
    redeems = Counter()
    burns  = Counter()
    contract = web3.eth.contract(awbtcAddress, abi=awbtcABI)
    for start in trange(8163813, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        mintLogs = contract.events.MintOnDeposit().getLogs(fromBlock=start, toBlock=end)
        redeemLogs = contract.events.Redeem().getLogs(fromBlock=start, toBlock=end)
        burnLogs = contract.events.BurnOnLiquidation().getLogs(fromBlock=start, toBlock=end)

        for log in mintLogs:
            mints[log['args']['_from']] += log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])

        for log in redeemLogs:
            redeems[log['args']['_from']] += log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])

        for log in burnLogs:
            burns[log['args']['_from']] += log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])

    filteredMints = valfilter(bool, dict(mints.most_common()))
    print(len(filteredMints))

    filteredRedeems = valfilter(bool, dict(redeems.most_common()))
    print(len(filteredRedeems))

    filteredBurns = valfilter(bool, dict(burns.most_common()))
    print(len(filteredBurns))

    final = Counter()
    for key in filteredMints:
        final[key] = filteredMints[key]

        if key in filteredBurns:
            final[key] = filteredMints[key] - filteredBurns[key]
        if key in filteredRedeems:
            final[key] = filteredMints[key] - filteredRedeems[key]
            
    filteredFinal = valfilter(bool, dict(final.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_awbtc_borrow():
    borrow = Counter()
    contract = web3.eth.contract(wbtcAddress, abi=wbtcABI)
    for start in trange(10151366, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['to'] == aaveLendAddress:
                borrow[log['args']['from']] -= log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['from'] == aaveLendAddress:
                borrow[log['args']['to']] += log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(borrow.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_cwbtc_borrow():
    borrow = Counter()
    contract = web3.eth.contract(wbtcAddress, abi=wbtcABI)
    for start in trange(10151366, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['to'] == cwbtcAddress:
                borrow[log['args']['from']] -= log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['from'] == cwbtcAddress:
                borrow[log['args']['to']] += log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(borrow.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_renbtc_liq():
    supply = Counter()
    contract = web3.eth.contract(renbtcLPAddress, abi=renbtcLPABI)
    for start in trange(10151366, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['_to'] == ZERO_ADDRESS:
                supply[log['args']['_from']] -= log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['_from'] == ZERO_ADDRESS:
                supply[log['args']['_to']] += log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(supply.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_sbtc_liq():
    supply = Counter()
    contract = web3.eth.contract(sbtcLPAddress, abi=sbtcLPABI)
    for start in trange(10276544, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['_to'] == ZERO_ADDRESS:
                supply[log['args']['_from']] -= log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['_from'] == ZERO_ADDRESS:
                supply[log['args']['_to']] += log['args']['_value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(supply.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_uni_liq():
    supply = Counter()
    contract = web3.eth.contract(uniWBTCETHAddress, abi=uniWBTCETHABI)
    for start in trange(10000835, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['to'] == ZERO_ADDRESS:
                supply[log['args']['from']] -= log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['from'] == ZERO_ADDRESS:
                supply[log['args']['to']] += log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(supply.most_common()))
    print(len(filteredFinal))

    return filteredFinal

def get_bal_liq():
    supply = Counter()
    contract = web3.eth.contract(wbtcBalAddress, abi=wbtcBalABI)
    for start in trange(10523862, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)

        for log in logs:
            if log['args']['dst'] == wbtcBalAddress:
                supply[log['args']['src']] -= log['args']['amt']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['src'] == wbtcBalAddress:
                supply[log['args']['dst']] += log['args']['amt']*(SNAPSHOT_BLOCK - log['blockNumber'])
            
    filteredFinal = valfilter(bool, dict(supply.most_common()))
    print(len(filteredFinal))

    return filteredFinal 

def get_wbtc_vaults():
    join = Counter()
    exits  = Counter()
    contract = web3.eth.contract(wbtcAddress, abi=wbtcABI)
    for start in trange(8163813, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['to'] == joinwbtcAddress:
                join[log['args']['from']] += log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])
            if log['args']['from'] == joinwbtcAddress:
                join[log['args']['to']] -= log['args']['value']*(SNAPSHOT_BLOCK - log['blockNumber'])

    filteredJoins = valfilter(bool, dict(join.most_common()))
    print(len(filteredJoins))

    return filteredJoins 

def clean_wbtc_vaults(vaults):
    clean = Counter()
    for key in vaults:
        clean[key] += vaults[key]
        contract = web3.eth.contract(key, abi=proxyABI)
        try:
            owner = contract.functions.owner().call()
            clean[owner] += vaults[key]
            clean[key] -= vaults[key]
        except:
            print("")

    filteredJoins = valfilter(bool, dict(clean.most_common()))
    print(len(filteredJoins))
    return filteredJoins 

def transfers_to_balances(address):
    balances = Counter()
    contract = web3.eth.contract(address, abi=DAI.abi)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['src'] != ZERO_ADDRESS:
                balances[log['args']['src']] -= log['args']['wad']
            if log['args']['dst'] != ZERO_ADDRESS:
                balances[log['args']['dst']] += log['args']['wad']

    return valfilter(bool, dict(balances.most_common()))

def get_stakers():
    balances = Counter()
    contract = web3.eth.contract(yfiAddress, abi=YFI.abi)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['dst'] == ygovAddress:
                balances[log['args']['src']] = 1

    filteredBals = valfilter(bool, dict(balances.most_common()))
    print(len(filteredBals))

    return filteredBals

def get_tippers():
    balances2 = Counter()
    trxFile = open("./scripts/transactions.txt", "r")
    contract = web3.eth.contract('0x5e37996bcfF8C169e77b00D7b6e7261bbC60761e', abi=merkleABI)

    for line in trxFile:
        line = line.replace("\n", "")
        trx = web3.eth.getTransaction(line)
        inp = contract.decode_function_input(trx.input)
        if str(inp[0]) == '<Function claim(uint256,address,uint256,bytes32[],uint256)>' and inp[1]['tipBips'] >= 100:
            balances2[inp[1]['account']] = 1

    filteredBals = valfilter(bool, dict(balances2.most_common()))

    print(len(filteredBals))
    return filteredBals

class MerkleTree:
    def __init__(self, elements):
        self.elements = sorted(set(web3.keccak(hexstr=el) for el in elements))
        self.layers = MerkleTree.get_layers(self.elements)

    @property
    def root(self):
        return self.layers[-1][0]

    def get_proof(self, el):
        el = web3.keccak(hexstr=el)
        idx = self.elements.index(el)
        proof = []
        for layer in self.layers:
            pair_idx = idx + 1 if idx % 2 == 0 else idx - 1
            if pair_idx < len(layer):
                proof.append(encode_hex(layer[pair_idx]))
            idx //= 2
        return proof

    @staticmethod
    def get_layers(elements):
        layers = [elements]
        while len(layers[-1]) > 1:
            layers.append(MerkleTree.get_next_layer(layers[-1]))
        return layers

    @staticmethod
    def get_next_layer(elements):
        return [MerkleTree.combined_hash(a, b) for a, b in zip_longest(elements[::2], elements[1::2])]

    @staticmethod
    def combined_hash(a, b):
        if a is None:
            return b
        if b is None:
            return a
        return web3.keccak(b''.join(sorted([a, b])))


@cached('snapshot/08-merkle-distribution.json')
def step_07(balances):
    elements = [(index, account, amount) for index, (account, amount) in enumerate(balances.items())]
    nodes = [encode_hex(encode_abi_packed(['uint', 'address', 'uint'], el)) for el in elements]
    tree = MerkleTree(nodes)
    distribution = {
        'merkleRoot': encode_hex(tree.root),
        'tokenTotal': hex(sum(balances.values())),
        'claims': {
            user: {'index': index, 'amount': hex(amount), 'proof': tree.get_proof(nodes[index])}
            for index, user, amount in elements
        },
    }
    print(f'merkle root: {encode_hex(tree.root)}')
    return distribution


def deploy():
    user = accounts[0] if rpc.is_active() else accounts.load(input('account: '))
    tree = json.load(open('snapshot/07-merkle-distribution.json'))
    root = tree['merkleRoot']
    token = str(DAI)
    MerkleDistributor.deploy(token, root, {'from': user})


def claim():
    claimer = accounts.load(input('Enter brownie account: '))
    dist = MerkleDistributor.at(DISTRIBUTOR_ADDRESS)
    tree = json.load(open('snapshot/07-merkle-distribution.json'))
    claim_other = input('Claim for another account? y/n [default: n] ') or 'n'
    assert claim_other in {'y', 'n'}
    user = str(claimer) if claim_other == 'n' else input('Enter address to claim for: ')

    if user not in tree['claims']:
        return secho(f'{user} is not included in the distribution', fg='red')
    claim = tree['claims'][user]
    if dist.isClaimed(claim['index']):
        return secho(f'{user} has already claimed', fg='yellow')

    amount = Wei(int(claim['amount'], 16)).to('ether')
    secho(f'Claimable amount: {amount} DAI', fg='green')
    if claim_other == 'n':  # no tipping for others
        secho(
            '\nThe return of funds to you was made possible by a team of volunteers who worked for free to make this happen.'
            '\nPlease consider tipping them a portion of your recovered funds as a way to say thank you.\n',
            fg='yellow',
        )
        tip = input('Enter tip amount in percent: ')
        tip = int(float(tip.rstrip('%')) * 100)
        assert 0 <= tip <= 10000, 'invalid tip amount'
    else:
        tip = 0

    tx = dist.claim(claim['index'], user, claim['amount'], claim['proof'], tip, {'from': claimer})
    tx.info()


def main():
    # minters = get_wbtc_mint()
    # print(len(minters))
    # with open('./snapshot/wbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_renbtc_mint()
    # print(len(minters))
    # with open('./snapshot/renbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_cwbtc_mint()
    # print(len(minters))
    # with open('./snapshot/cwbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_awbtc_mint()
    # print(len(minters))
    # with open('./snapshot/awbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_wbtc_holders()
    # print(len(minters))
    # with open('./snapshot/wbtcHolders.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_renbtc_holders()
    # print(len(minters))
    # with open('./snapshot/renbtcHolders.json', 'w') as fp:
    #     json.dump(minters, fp)

    # lps = get_renbtc_liq()
    # print(len(lps))
    # with open('./snapshot/renbtcLP.json', 'w') as fp:
    #     json.dump(lps, fp)
    
    # lps = get_sbtc_liq()
    # print(len(lps))
    # with open('./snapshot/sbtcLP.json', 'w') as fp:
    #     json.dump(lps, fp)

    # lps = get_uni_liq()
    # print(len(lps))
    # with open('./snapshot/uniLP.json', 'w') as fp:
    #     json.dump(lps, fp)

    # lps = get_bal_liq()
    # print(len(lps))
    # with open('./snapshot/balLP.json', 'w') as fp:
    #     json.dump(lps, fp)

    # minters = get_wbtc_vaults()
    # print(len(minters))
    # with open('./snapshot/wbtcMaker.json', 'w') as fp:
    #     json.dump(minters, fp)

    # with open('./snapshot/wbtcMaker.json', 'r') as reader, open('./snapshot/finalwbtcMaker.json', 'w') as writer:
    #     maker = json.load(reader)
    #     clean = clean_wbtc_vaults(maker)
    #     json.dump(clean, writer)

    # minters = get_sbtc_mint()
    # print(len(minters))
    # with open('./snapshot/sbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_awbtc_borrow()
    # print(len(minters))
    # with open('./snapshot/awbtcBorrow.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_cwbtc_borrow()
    # print(len(minters))
    # with open('./snapshot/cwbtcBorrow.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_tbtc_mint()
    # print(len(minters))
    # with open('./snapshot/tbtcMinters.json', 'w') as fp:
    #     json.dump(minters, fp)

    # minters = get_meta()
    # print(len(minters))
    # with open('./snapshot/meta.json', 'w') as fp:
    #     json.dump(minters, fp)

    # num_s = YGOV_AMOUNT / len(stakers)
    # for key in stakers:    
    #     stakers[key] *=  num_s
    # with open('./snapshot/stakers.json', 'w') as fp:
    #     json.dump(stakers, fp)
    # print('got stakers')

    # with open('./snapshot/stakers.json') as json_file:
    #     stakers = json.load(json_file)

    # for key in stakers:    
    #     stakers[key] =  Wei(stakers[key])

    final = Counter()
    grandTotal = 0
    total = 0
    check = 0
    with open('./snapshot/awbtcMinters.json') as json_file:
        awbtcM = json.load(json_file)

    for key in awbtcM:
        total += awbtcM[key]

    for key in awbtcM:    
        awbtcM[key] =  Wei((awbtcM[key]/total)*62874251500000000000000)
        check += awbtcM[key]
        final[key] += awbtcM[key]
    
    print("Aave LP:", Wei(check).to("ether"))
    
    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/awbtcBorrow.json') as json_file:
        awbtcB = json.load(json_file)

    for key in awbtcB:
        total += awbtcB[key]

    for key in awbtcB:    
        awbtcB[key] =  Wei((awbtcB[key]/total)*62874251500000000000000)
        check += awbtcB[key]
        final[key] += awbtcB[key]
    
    print("Aave Borrow:", Wei(check).to("ether"))
    
    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/balLP.json') as json_file:
        balLP = json.load(json_file)

    for key in balLP:
        total += balLP[key]

    for key in balLP:    
        balLP[key] =  Wei((balLP[key]/total)*125748503000000000000000)
        check += balLP[key]
        final[key] += balLP[key]
    
    print("Balance LP:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/cwbtcMinters.json') as json_file:
        cwbtc = json.load(json_file)

    for key in cwbtc:
        total += cwbtc[key]

    for key in cwbtc:    
        cwbtc[key] =  Wei((cwbtc[key]/total)*62874251500000000000000)
        check += cwbtc[key]
        final[key] += cwbtc[key]
    
    print("Comp LP:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/cwbtcBorrow.json') as json_file:
        cwbtc = json.load(json_file)

    for key in cwbtc:
        total += cwbtc[key]

    for key in cwbtc:    
        cwbtc[key] =  Wei((cwbtc[key]/total)*62874251500000000000000)
        check += cwbtc[key]
        final[key] += cwbtc[key]
    
    print("Comp Borrow:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/dorgx.json') as json_file:
        dorgx = json.load(json_file)

    for key in dorgx:
        total += dorgx[key]

    for key in dorgx:    
        dorgx[key] =  Wei((dorgx[key]/total)*12574850300000000000000)
        check += dorgx[key]
        final[key] += dorgx[key]
    
    print("dOrgx Member:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/finalwbtcMaker.json') as json_file:
        maker = json.load(json_file)

    for key in maker:
        total += maker[key]

    for key in maker:    
        maker[key] =  Wei((maker[key]/total)*125748503000000000000000)
        check += maker[key]
        final[key] += maker[key]
    
    print("Maker Borrow:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/gitcoin.json') as json_file:
        gitcoin = json.load(json_file)

    for key in gitcoin:
        total += gitcoin[key]

    for key in gitcoin:    
        gitcoin[key] =  Wei((gitcoin[key]/total)*251497006000000000000000)
        check += gitcoin[key]
        final[key] += gitcoin[key]
    
    print("Gitcoin:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/harvest.json') as json_file:
        harvest = json.load(json_file)

    for key in harvest:
        total += harvest[key]

    for key in harvest:    
        harvest[key] =  Wei((harvest[key]/total)*25149700600000000000000)
        check += harvest[key]
        final[key] += harvest[key]
    
    print("Harvest Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/yam.json') as json_file:
        yam = json.load(json_file)

    for key in yam:
        total += yam[key]

    for key in yam:    
        yam[key] =  Wei((yam[key]/total)*25149700600000000000000)
        check += yam[key]
        final[key] += yam[key]
    
    print("YAM Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/lao.json') as json_file:
        lao = json.load(json_file)

    for key in lao:
        total += lao[key]

    for key in lao:    
        lao[key] =  Wei((lao[key]/total)*12574850300000000000000)
        check += lao[key]
        final[key] += lao[key]
    
    print("LAO Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/meta.json') as json_file:
        meta = json.load(json_file)

    for key in meta:
        total += meta[key]

    for key in meta:    
        meta[key] =  Wei((meta[key]/total)*12574850300000000000000)
        check += meta[key]
        final[key] += meta[key]
    
    print("META Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/renbtcLP.json') as json_file:
        renbtcLP = json.load(json_file)

    for key in renbtcLP:
        total += renbtcLP[key]

    for key in renbtcLP:    
        renbtcLP[key] =  Wei((renbtcLP[key]/total)*251497006000000000000000)
        check += renbtcLP[key]
        final[key] += renbtcLP[key]
    
    print("Ren LP:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/sbtcLP.json') as json_file:
        sbtcLP = json.load(json_file)

    for key in sbtcLP:
        total += sbtcLP[key]

    for key in sbtcLP:    
        sbtcLP[key] =  Wei((sbtcLP[key]/total)*251497006000000000000000)
        check += sbtcLP[key]
        final[key] += sbtcLP[key]
    
    print("sBTC LP:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/sbtcMinters.json') as json_file:
        sbtcMinters = json.load(json_file)

    for key in sbtcMinters:
        total += sbtcMinters[key]

    for key in sbtcMinters:    
        sbtcMinters[key] =  Wei((sbtcMinters[key]/total)*62874251500000000000000)
        check += sbtcMinters[key]
        final[key] += sbtcMinters[key]
    
    print("sBTC Minters:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/stakers.json') as json_file:
        yfiStakers = json.load(json_file)

    for key in yfiStakers:
        total += yfiStakers[key]

    for key in yfiStakers:    
        yfiStakers[key] =  Wei((yfiStakers[key]/total)*188622754500000000000000)
        check += yfiStakers[key]
        final[key] += yfiStakers[key]
    
    print("YFI Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/sushi.json') as json_file:
        sushi = json.load(json_file)

    for key in sushi:
        total += sushi[key]

    for key in sushi:    
        sushi[key] =  Wei((sushi[key]/total)*62874251500000000000000)
        check += sushi[key]
        final[key] += sushi[key]
    
    print("SUSHI Gov:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/tbtcMinters.json') as json_file:
        tbtcMinters = json.load(json_file)

    for key in tbtcMinters:
        total += tbtcMinters[key]

    for key in tbtcMinters:    
        tbtcMinters[key] =  Wei((tbtcMinters[key]/total)*125748503000000000000000)
        check += tbtcMinters[key]
        final[key] += tbtcMinters[key]
    
    print("TBTC Minter:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/uniLP.json') as json_file:
        uniLP = json.load(json_file)

    for key in uniLP:
        total += uniLP[key]

    for key in uniLP:    
        uniLP[key] =  Wei((uniLP[key]/total)*125748503000000000000000)
        check += uniLP[key]
        final[key] += uniLP[key]
    
    print("Uniswap LP:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/wbtcHolders.json') as json_file:
        wbtcHolders = json.load(json_file)

    for key in wbtcHolders:
        total += wbtcHolders[key]

    for key in wbtcHolders:    
        wbtcHolders[key] =  Wei((wbtcHolders[key]/total)*62874251500000000000000)
        check += wbtcHolders[key]
        final[key] += wbtcHolders[key]
    
    print("WBTC Holders:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/renbtcHolders.json') as json_file:
        renbtcHolders = json.load(json_file)

    for key in renbtcHolders:
        total += renbtcHolders[key]

    for key in renbtcHolders:    
        renbtcHolders[key] =  Wei((renbtcHolders[key]/total)*62874251500000000000000)
        check += renbtcHolders[key]
        final[key] += renbtcHolders[key]
    
    print("renBTC Holders:", Wei(check).to("ether"))

    grandTotal += check
    total = 0
    check = 0
    with open('./snapshot/wbtcMinters.json') as json_file:
        merchants = json.load(json_file)

    for key in merchants:
        total += merchants[key]

    for key in merchants:    
        merchants[key] =  Wei((merchants[key]/total)*37724550900000000000000)
        check += merchants[key]
        final[key] += merchants[key]
    
    print("WBTC Merchants:", Wei(check).to("ether"))
    grandTotal += check


    print("Total:", Wei(grandTotal).to("ether"))
    print("Missing:", Wei(2100000000000000000000000-grandTotal).to("ether"))

    with open('./snapshot/final.json', 'w') as fp:
        json.dump(final, fp)
    step_07(final)
