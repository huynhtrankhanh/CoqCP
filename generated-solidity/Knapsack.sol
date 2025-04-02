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

    function communicationGet(bytes memory communication, uint64 index) private returns (uint8) {
        if (index >= communication.length) { assembly { revert(0, 0) } }
        return uint8(communication[index]);
    }

    function communicationSet(bytes memory communication, uint64 index, uint8 value) private {
        if (index >= communication.length) { assembly { revert(0, 0) } }
        communication[index] = bytes1(value);
    }

    function sdivint8(int8 a, int8 b) private returns (int8) {
        if ((b == -1 && a == type(int8).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint8(uint8 a, uint8 b) private returns (uint8) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function sdivint16(int16 a, int16 b) private returns (int16) {
        if ((b == -1 && a == type(int16).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint16(uint16 a, uint16 b) private returns (uint16) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function sdivint32(int32 a, int32 b) private returns (int32) {
        if ((b == -1 && a == type(int32).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint32(uint32 a, uint32 b) private returns (uint32) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function sdivint64(int64 a, int64 b) private returns (int64) {
        if ((b == -1 && a == type(int64).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint64(uint64 a, uint64 b) private returns (uint64) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function sdivint256(int256 a, int256 b) private returns (int256) {
        if ((b == -1 && a == type(int256).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint256(uint256 a, uint256 b) private returns (uint256) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    struct Tuple0 {
        uint64 item0;
    }

    function arrayGet(Tuple0[] storage array, uint64 index) private returns (Tuple0 memory) {
        if (index >= array.length) { assembly { revert(0, 0) } }
        return array[index];
    }

    function arraySet(Tuple0[] storage array, uint64 index, Tuple0 memory value) private {
        if (index >= array.length) { assembly { revert(0, 0) } }
        array[index] = value;
    }

    Tuple0[] private environment0;
    struct Tuple1 {
        uint32 item0;
    }

    function arrayGet(Tuple1[] storage array, uint64 index) private returns (Tuple1 memory) {
        if (index >= array.length) { assembly { revert(0, 0) } }
        return array[index];
    }

    function arraySet(Tuple1[] storage array, uint64 index, Tuple1 memory value) private {
        if (index >= array.length) { assembly { revert(0, 0) } }
        array[index] = value;
    }

    Tuple1[] private environment1;
    Tuple0[] private environment2;

    constructor() {
        for (uint i = 0; i < 1000000; i++) environment0.push(Tuple0(0));
        for (uint i = 0; i < 1; i++) environment1.push(Tuple1(0));
        for (uint i = 0; i < 1; i++) environment2.push(Tuple0(0));
    }
    function procedure0(Tuple0[] storage environment0, Tuple1[] storage environment1, Tuple0[] storage environment2, uint64 local0, bytes memory communication) private { unchecked {
        arraySet(environment1, uint64(0), Tuple1(((((uint32(communicationGet(communication, (uint64(4) * local0))) * uint32((uint64(1) << uint64(24)))) + (uint32(communicationGet(communication, ((uint64(4) * local0) + uint64(1)))) * uint32((uint64(1) << uint64(16))))) + (uint32(communicationGet(communication, ((uint64(4) * local0) + uint64(2)))) * uint32((uint64(1) << uint64(8))))) + uint32(communicationGet(communication, ((uint64(4) * local0) + uint64(3)))))));
    } }

    function procedure1(Tuple0[] storage environment0, Tuple1[] storage environment1, Tuple0[] storage environment2, uint64 local0, bytes memory communication) private { unchecked {
        arraySet(environment1, uint64(0), Tuple1(((((uint32(communicationGet(communication, ((uint64(4) * arrayGet(environment2, uint64(0)).item0) + (uint64(4) * local0)))) * uint32((uint64(1) << uint64(24)))) + (uint32(communicationGet(communication, (((uint64(4) * arrayGet(environment2, uint64(0)).item0) + (uint64(4) * local0)) + uint64(1)))) * uint32((uint64(1) << uint64(16))))) + (uint32(communicationGet(communication, (((uint64(4) * arrayGet(environment2, uint64(0)).item0) + (uint64(4) * local0)) + uint64(2)))) * uint32((uint64(1) << uint64(8))))) + uint32(communicationGet(communication, (((uint64(4) * arrayGet(environment2, uint64(0)).item0) + (uint64(4) * local0)) + uint64(3)))))));
    } }

    function procedure2(Tuple0[] storage environment0, Tuple1[] storage environment1, Tuple0[] storage environment2, uint64 local0, bytes memory communication) private { unchecked {
        communicationSet(communication, uint64(0), uint8((local0 >> uint64(56))));
        communicationSet(communication, uint64(1), uint8(((local0 >> uint64(48)) & uint64(255))));
        communicationSet(communication, uint64(2), uint8(((local0 >> uint64(40)) & uint64(255))));
        communicationSet(communication, uint64(3), uint8(((local0 >> uint64(32)) & uint64(255))));
        communicationSet(communication, uint64(4), uint8(((local0 >> uint64(24)) & uint64(255))));
        communicationSet(communication, uint64(5), uint8(((local0 >> uint64(16)) & uint64(255))));
        communicationSet(communication, uint64(6), uint8(((local0 >> uint64(8)) & uint64(255))));
        communicationSet(communication, uint64(7), uint8((local0 & uint64(255))));
    } }

    function procedure3(Tuple0[] storage environment0, Tuple1[] storage environment1, Tuple0[] storage environment2, bytes memory communication) private { unchecked {
        arraySet(environment1, uint64(0), Tuple1(((((uint32(communicationGet(communication, (uint64(8) * arrayGet(environment2, uint64(0)).item0))) * uint32((uint64(1) << uint64(24)))) + (uint32(communicationGet(communication, (uint64(8) * arrayGet(environment2, uint64(0)).item0))) * uint32((uint64(1) << uint64(16))))) + (uint32(communicationGet(communication, (uint64(8) * arrayGet(environment2, uint64(0)).item0))) * uint32((uint64(1) << uint64(8))))) + uint32(communicationGet(communication, (uint64(8) * arrayGet(environment2, uint64(0)).item0))))));
    } }

    function procedure4(Tuple0[] storage environment0, Tuple1[] storage environment1, Tuple0[] storage environment2, bytes memory communication) private { unchecked {
        arraySet(environment2, uint64(0), Tuple0(divint64(((uint64(msg.data.length) - uint64(4))), (uint64(8)))));
    } }

    fallback() external payable {
        bytes memory data = msg.data;
        procedure4(environment0, environment1, environment2, data);
        assembly {
            return(add(data, 0x20), mload(data))
        }
    }
}
