methods {
    // IERC721
    function balanceOf(address) external returns (uint256) envfree;
    function ownerOf(uint256) external returns (address) envfree;
    function getApproved(uint256) external returns (address) envfree;
    function isApprovedForAll(address,address) external returns (bool) envfree;
    function safeTransferFrom(address,address,uint256,bytes) external;
    function safeTransferFrom(address,address,uint256) external;
    function transferFrom(address,address,uint256) external;
    function approve(address,uint256) external;
    function setApprovalForAll(address,bool) external;
    function tokenOfOwnerByIndex(address, uint256) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;

    // IERC721Metadata
    function name() external returns (string);
    function symbol() external returns (string);
    function tokenURI(uint256) external returns (string) => NONDET DELETE;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Ghost & hooks: Tokens array                                                                                      │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

ghost uint256 NumberOfTokens {init_state axiom NumberOfTokens == 0;}

hook Sload uint256 _length _allTokens.(offset 0) STORAGE {
    require NumberOfTokens == _length;
}

hook Sstore _allTokens.(offset 0) uint256 _length (uint256 _length_old) STORAGE {
    require NumberOfTokens == _length_old;
    NumberOfTokens = _length;
}

ghost mapping(uint256 => uint256) TokenAtIndex {
    init_state axiom forall uint256 index. TokenAtIndex[index] == 0;
}

hook Sload uint256 tokenID _allTokens[INDEX uint256 indx] STORAGE {
    require TokenAtIndex[indx] == tokenID;
}

hook Sstore _allTokens[INDEX uint256 indx] uint256 tokenID (uint256 tokenID_old) STORAGE {
    require TokenAtIndex[indx] == tokenID_old;
    TokenAtIndex[indx] = tokenID;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Ghost & hooks: Tokens indices                                                                                      │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

ghost mapping(uint256 => uint256) tokensIndex {
    init_state axiom forall uint256 tokenID. tokensIndex[tokenID] == 0;
}

hook Sload uint256 index _allTokensIndex[KEY uint256 tokenID] STORAGE {
    require tokensIndex[tokenID] == index;
}

hook Sstore _allTokensIndex[KEY uint256 tokenID] uint256 index (uint256 index_old) STORAGE {
    require tokensIndex[tokenID] == index_old;
    tokensIndex[tokenID] = index;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Invariants: Enumerable tokens                                                                                     │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

invariant TokenBalanceIsZeroOrOne(address account)
    balanceOf(account) ==0 || balanceOf(account) == 1
    filtered{f -> !upgradeMethods(f)}

invariant BalanceOfZero()
    balanceOf(0) == 0;

invariant ZeroAddressNotKYC(env e)
    !viewer.isKYC(e,0)
    {
        preserved with (env eP) {
            requireInvariant ZeroAddressNotKYC(eP);
            requireInvariant BalanceOfZero();
        }
    }

invariant IsOwnedInTokensArray(uint256 tokenID)
    ownerOf(tokenID) !=0 => totalSupply() > 0
    filtered{f -> !upgradeMethods(f)}
    {
        preserved with (env e) {
            require totalSupply() < max_uint256;
        }
        preserved burn(uint256 _tokenID) with (env e) {
            require totalSupply() < max_uint256;
            require ownerOf(_tokenID) !=0 => totalSupply() > 1;
        }
        preserved burnKYC(IKintoID.SignatureData data) with (env e) {
            require totalSupply() < max_uint256;
            require ownerOf(tokenOfOwnerByIndex(data.signer, 0)) !=0 => totalSupply() > 1;
        }
    }

invariant TokenIndexIsUpToArrayLength(uint256 tokenID)
    forall uint256 _tokenID. NumberOfTokens == 0 ? 
        (tokensIndex[_tokenID] == 0) : tokensIndex[_tokenID] < NumberOfTokens
    {
        preserved {
            requireInvariant TokenAtIndexConsistency();
            uint256 tokenIDEnd;
            require tokensIndex[tokenIDEnd] == (NumberOfTokens == 0 ? 0 : assert_uint256(NumberOfTokens - 1));
            requireInvariant NoOwnerNoIndex(tokenIDEnd);
            require NumberOfTokens < max_uint256;
        }
    }

invariant TokenAtIndexConsistency()
    (forall uint256 index. 
        (index < NumberOfTokens => tokensIndex[TokenAtIndex[index]] == index) &&
        (index >= NumberOfTokens => TokenAtIndex[index] == 0))
    &&
    (forall uint256 tokenID.
        tokensIndex[tokenID] !=0 => TokenAtIndex[tokensIndex[tokenID]] == tokenID)
    &&
    tokensIndex[0] == 0
    {
        preserved {
            require NumberOfTokens < max_uint256;
            requireInvariant NoOwnerNoIndex(require_uint256(nextTokenId()+1));
        }
    }

invariant NoOwnerNoIndex(uint256 tokenID)
    ownerOf(tokenID) == 0 => tokensIndex[tokenID] == 0;
