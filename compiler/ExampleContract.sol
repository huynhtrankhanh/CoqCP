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

    Tuple0[] public environment0;
    Tuple0[] public environment1;
    struct Tuple1 {
        uint8 item0;
    }

    Tuple1[] public environment2;

    constructor() {
        environment0 = new Tuple0[](1);
        environment1 = new Tuple0[](1);
        environment2 = new Tuple1[](1024);
    }
    function procedure0(Tuple0[] storage environment0, Tuple0[] storage environment1, Tuple1[] storage environment2, uint32 local0, address local1, bytes memory communication) private { unchecked {
        local0 = ((((uint32(uint8(communication[uint64(0)])) << uint32(uint64(24))) + (uint32(uint8(communication[uint64(1)])) << uint32(uint64(16)))) + (uint32(uint8(communication[uint64(2)])) << uint32(uint64(8)))) + uint32(uint8(communication[uint64(3)])));
        if ((environment1[uint64(0)].item0 == uint32(uint64(0)))) {
            environment0[uint64(0)] = Tuple0(local0);
        } else {
        }
        if ((local0 == environment0[uint64(0)].item0)) {
            environment1[uint64(0)] = Tuple0((environment1[uint64(0)].item0 + uint32(uint64(1))));
        } else {
            environment1[uint64(0)] = Tuple0((environment1[uint64(0)].item0 - uint32(uint64(1))));
        }
        communication[uint64(0)] = bytes1(uint8((environment1[uint64(0)].item0 >> uint32(uint64(24)))));
        communication[uint64(1)] = bytes1(uint8(((environment1[uint64(0)].item0 >> uint32(uint64(16))) & uint32(uint64(255)))));
        communication[uint64(2)] = bytes1(uint8(((environment1[uint64(0)].item0 >> uint32(uint64(8))) & uint32(uint64(255)))));
        communication[uint64(3)] = bytes1(uint8((environment1[uint64(0)].item0 & uint32(uint64(255)))));
        shoot(payable(local1), uint256(uint64(2000)));
        {
            uint64 communicationSize = uint64(uint64(1024));
            bytes memory callData = new bytes(communicationSize);
            for (uint i = 0; i < communicationSize; i++) callData[i] = bytes1(environment2[i].item0);
            (bool success, bytes memory returnData) = address(local1).call{value: uint256(uint64(2000))}(callData);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = Tuple1(uint8(returnData[i]));
        }
        {
            uint64 communicationSize = uint64(uint64(1024));
            bytes memory callData = new bytes(communicationSize);
            for (uint i = 0; i < communicationSize; i++) callData[i] = bytes1(environment2[i].item0);
            (bool success, bytes memory returnData) = address(msg.sender).call{value: msg.value}(callData);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = Tuple1(uint8(returnData[i]));
        }
        {
            uint64 communicationSize = uint64(uint64(1024));
            bytes memory callData = new bytes(communicationSize);
            for (uint i = 0; i < communicationSize; i++) callData[i] = bytes1(environment2[i].item0);
            (bool success, bytes memory returnData) = address(constructAddress(uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)), uint8(uint64(0)))).call{value: msg.value}(callData);
            for (uint i = 0; i < communicationSize && i < returnData.length; i++)
                environment2[i] = Tuple1(uint8(returnData[i]));
        }
    } }

    fallback() external payable {
        bytes memory data = msg.data;
        procedure0(environment0, environment1, environment2, 0, address(0), data);
        assembly {
            return(add(data, 0x20), mload(data))
        }
    }
}
