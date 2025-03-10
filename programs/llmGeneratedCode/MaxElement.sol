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


    constructor() {
    }
    function procedure0(uint64 local0, uint64 local1, uint64 local2, uint64 local3, bytes memory communication) private { unchecked {
        local0 = divint256((msg.data.length), (uint64(uint64(8))));
        if ((local0 != uint64(uint64(0)))) {
            local1 = ((((((((uint64(communicationGet(communication, uint64(uint64(0)))) * uint64(uint64(72057594037927936))) + (uint64(communicationGet(communication, uint64(uint64(1)))) * uint64(uint64(281474976710656)))) + (uint64(communicationGet(communication, uint64(uint64(2)))) * uint64(uint64(1099511627776)))) + (uint64(communicationGet(communication, uint64(uint64(3)))) * uint64(uint64(4294967296)))) + (uint64(communicationGet(communication, uint64(uint64(4)))) * uint64(uint64(16777216)))) + (uint64(communicationGet(communication, uint64(uint64(5)))) * uint64(uint64(65536)))) + (uint64(communicationGet(communication, uint64(uint64(6)))) * uint64(uint64(256)))) + uint64(communicationGet(communication, uint64(uint64(7)))));
            for (uint64 binder0 = 0; binder0 < (local0 - uint64(uint64(1))); binder0++) {
                local2 = ((binder0 + uint64(uint64(1))) * uint64(uint64(8)));
                local3 = ((((((((uint64(communicationGet(communication, local2)) * uint64(uint64(72057594037927936))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(1))))) * uint64(uint64(281474976710656)))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(2))))) * uint64(uint64(1099511627776)))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(3))))) * uint64(uint64(4294967296)))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(4))))) * uint64(uint64(16777216)))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(5))))) * uint64(uint64(65536)))) + (uint64(communicationGet(communication, (local2 + uint64(uint64(6))))) * uint64(uint64(256)))) + uint64(communicationGet(communication, (local2 + uint64(uint64(7))))));
                if ((local1 < local3)) {
                    local1 = local3;
                } else {
                }
            }
        } else {
            local1 = uint64(uint64(0));
        }
        communicationSet(communication, uint64(0), uint8(divint64((local1), (uint64(uint64(72057594037927936))))));
        communicationSet(communication, uint64(1), uint8((divint64((local1), (uint64(uint64(281474976710656)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(2), uint8((divint64((local1), (uint64(uint64(1099511627776)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(3), uint8((divint64((local1), (uint64(uint64(4294967296)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(4), uint8((divint64((local1), (uint64(uint64(16777216)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(5), uint8((divint64((local1), (uint64(uint64(65536)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(6), uint8((divint64((local1), (uint64(uint64(256)))) % uint64(uint64(256)))));
        communicationSet(communication, uint64(7), uint8((local1 % uint64(uint64(256)))));
    } }

}
