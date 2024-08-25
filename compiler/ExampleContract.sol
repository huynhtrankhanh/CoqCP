// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract SelfDestructContract {
    constructor(address payable _target) payable {
        // Transfer all the ether stored in this contract to the target address and self-destruct
        selfdestruct(_target);
    }
}
  
contract GeneratedCode {
    function constructAddress(
        uint8 p0, uint8 p1, uint8 p2, uint8 p3, uint8 p4,
        uint8 p5, uint8 p6, uint8 p7, uint8 p8, uint8 p9,
        uint8 p10, uint8 p11, uint8 p12, uint8 p13, uint8 p14,
        uint8 p15, uint8 p16, uint8 p17, uint8 p18, uint8 p19
    ) private pure returns (address) {
        bytes memory packed = abi.encodePacked(
            p0, p1, p2, p3, p4, p5, p6, p7, p8, p9,
            p10, p11, p12, p13, p14, p15, p16, p17, p18, p19
        );
        return address(bytes20(packed));
    }

    function shoot(address payable _target, uint256 _wei) private {
        new SelfDestructContract{value: _wei}(_target);
    }

    struct Tuple0 {
        uint32 item0;
    }

    Tuple0[1] public current;
    Tuple0[1] public count;
    struct Tuple1 {
        uint8 item0;
    }

    Tuple1[1024] public scratchpad;

    function procedure0(Tuple0[] memory environment0, Tuple0[] memory environment1, Tuple1[] memory environment2, uint32 local0, address local1, bytes memory communication) private { unchecked {
        local0 = ((((uint32(communication[uint64(0)]) << uint32(uint64(24))) + (uint32(communication[uint64(1)]) << uint32(uint64(16)))) + (uint32(communication[uint64(2)]) << uint32(uint64(8)))) + uint32(communication[uint64(3)]));
        if ((environment1[uint64(0)].item0 == uint32(uint64(0)))) {
            environment0[uint64(0)] = Tuple0(local0);
        } else {
        }
        if ((local0 == environment0[uint64(0)].item0)) {
            environment1[uint64(0)] = Tuple0((environment1[uint64(0)].item0 + uint32(uint64(1))));
        } else {
            environment1[uint64(0)] = Tuple0((environment1[uint64(0)].item0 - uint32(uint64(1))));
        }
        communication[uint64(0)] = (environment1[uint64(0)].item0 >> uint32(uint64(24)));
        communication[uint64(1)] = ((environment1[uint64(0)].item0 >> uint32(uint64(16))) & uint32(uint64(255)));
        communication[uint64(2)] = ((environment1[uint64(0)].item0 >> uint32(uint64(8))) & uint32(uint64(255)));
        communication[uint64(3)] = (environment1[uint64(0)].item0 & uint32(uint64(255)));
        shoot(local1, uint256(uint64(2000)));
        {
            uint64 communicationSize = uint64(uint64(1024));
            (bool success, bytes memory returnData) = address(local1).call{value: uint256(uint64(2000))}(environment2[0:communicationSize]);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = returnData[i];
        }
        {
            uint64 communicationSize = uint64(uint64(1024));
            (bool success, bytes memory returnData) = address(msg.sender).call{value: msg.value}(environment2[0:communicationSize]);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = returnData[i];
        }
        {
            uint64 communicationSize = uint64(uint64(1024));
            (bool success, bytes memory returnData) = address(constructAddress(uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)))).call{value: msg.value}(environment2[0:communicationSize]);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = returnData[i];
        }
    } }

    fallback() external payable {
                main(current, count, scratchpad, 0, 0);
            }

}
