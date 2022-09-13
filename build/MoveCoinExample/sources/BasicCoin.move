module NamedAddr::BasicCoin{
    use std::signer;


    /// Address of the owner of this module
    const MODULE_OWNER: address = @NamedAddr;

    /// Error codes
    const ENOT_MODULE_OWNER: u64 = 0;
    const EINSUFFICIENT_BALANCE: u64 = 1;
    const EALREADY_HAS_BALANCE: u64 = 2;

    struct Coin<phantom CoinType> has store {
        value: u64,
    }

    /// Struct representing the balance of each address.
    struct Balance<phantom CoinType> has key {
        coin: Coin<CoinType> // same Coin from Step 1
    }

    /// Publish an empty balance resource under `account`'s address. This function must be called before
    /// minting or transferring to the account.
    public fun publish_balance<CoinType>(account: &signer) { 
        // an assert to check that `account` doesn't already have a `Balance` resource.
        assert!(!exists<Balance<CoinType>>(signer::address_of(account)), EALREADY_HAS_BALANCE);
        let empty_coin = Coin<CoinType> { value: 0 };
        move_to(account, Balance<CoinType> { coin:  empty_coin });
    }

    /// Mint `amount` tokens to `mint_addr`. Mint must be approved by the module owner.
    public fun mint<CoinType: drop>(mint_addr: address, amount: u64, _witness: CoinType) acquires Balance {  
        // Deposit `amount` of tokens to `mint_addr`'s balance
        deposit<CoinType>(mint_addr, Coin { value: amount });
    }

    /// Returns the balance of `owner`.
    public fun balance_of<CoinType>(owner: address): u64 acquires Balance {
        borrow_global<Balance<CoinType>>(owner).coin.value
    }

    /// Transfers `amount` of tokens from `from` to `to`.
    public fun transfer<CoinType: drop>(from: &signer, to: address, amount: u64, _witness: CoinType) acquires Balance {  
        let check = withdraw<CoinType>(signer::address_of(from), amount);
        deposit(to, check);
    }

    /// Withdraw `amount` number of tokens from the balance under `addr`.
    fun withdraw<CoinType>(addr: address, amount: u64) : Coin<CoinType> acquires Balance {
        let balance = balance_of<CoinType>(addr);
        // balance must be greater than the withdraw amount
        assert!(balance >= amount, EINSUFFICIENT_BALANCE);
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        *balance_ref = balance - amount;
        Coin<CoinType> { value: amount }
    }

    /// Deposit `amount` number of tokens to the balance under `addr`.
    fun deposit<CoinType>(addr: address, check: Coin<CoinType>) acquires Balance {
        let balance = balance_of<CoinType>(addr);
        // Get a mutable reference of addr's balance's coin value
        let balance_ref = &mut borrow_global_mut<Balance<CoinType>>(addr).coin.value;
        // unpacks the check
        let Coin { value } = check;
        // Increment the value by `value`
        *balance_ref = balance + value;
    }

}