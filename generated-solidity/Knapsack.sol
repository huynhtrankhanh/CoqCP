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

    constructor() {
        for (uint i = 0; i < 1000000; i++) environment0.push(Tuple0(0));
    }
    function procedure0(Tuple0[] storage environment0, uint64 local0, uint64 local1, uint64 local2, uint64 local3, uint64 local4, uint64 local5, uint64 local6, uint64 local7, uint64 local8, uint64 local9, uint64 local10, uint64 local11, uint64 local12, uint64 local13, uint64 local14, uint64 local15, uint64 local16, uint64 local17, uint64 local18, uint64 local19, uint64 local20, uint64 local21, uint64 local22, uint64 local23, uint64 local24, uint64 local25, uint64 local26, uint64 local27, uint64 local28, uint64 local29, uint64 local30, uint64 local31, uint64 local32, uint64 local33, uint64 local34, uint64 local35, uint64 local36, uint64 local37, uint64 local38, uint64 local39, bytes memory communication) private { unchecked {
        local0 = uint64(msg.data.length);
        if ((local0 < uint64(uint64(8)))) {
        } else {
            local1 = (local0 - uint64(uint64(4)));
            local2 = (local1 % uint64(uint64(8)));
            if ((local2 != uint64(uint64(0)))) {
            } else {
                local3 = divint64((local1), (uint64(uint64(8))));
                local4 = (local3 * uint64(uint64(8)));
                local5 = (uint64(communicationGet(communication, local4)) & uint64(uint64(255)));
                local6 = (uint64(communicationGet(communication, (local4 + uint64(uint64(1))))) & uint64(uint64(255)));
                local7 = (uint64(communicationGet(communication, (local4 + uint64(uint64(2))))) & uint64(uint64(255)));
                local8 = (uint64(communicationGet(communication, (local4 + uint64(uint64(3))))) & uint64(uint64(255)));
                local9 = ((((local5 << uint64(uint64(24))) | (local6 << uint64(uint64(16)))) | (local7 << uint64(uint64(8)))) | local8);
                local10 = (local9 + uint64(uint64(1)));
                local11 = ((local3 + uint64(uint64(1))) * local10);
                if ((uint64(uint64(1000000)) < local11)) {
                } else {
                    for (uint64 binder0 = 0; binder0 < local3; binder0++) {
                        local13 = (local12 + uint64(uint64(1)));
                        local14 = (local13 - uint64(uint64(1)));
                        local15 = (local14 * uint64(uint64(4)));
                        local16 = (uint64(communicationGet(communication, local15)) & uint64(uint64(255)));
                        local17 = (uint64(communicationGet(communication, (local15 + uint64(uint64(1))))) & uint64(uint64(255)));
                        local18 = (uint64(communicationGet(communication, (local15 + uint64(uint64(2))))) & uint64(uint64(255)));
                        local19 = (uint64(communicationGet(communication, (local15 + uint64(uint64(3))))) & uint64(uint64(255)));
                        local20 = ((((local16 << uint64(uint64(24))) | (local17 << uint64(uint64(16)))) | (local18 << uint64(uint64(8)))) | local19);
                        local21 = ((uint64(uint64(4)) * local3) + (local14 * uint64(uint64(4))));
                        local22 = (uint64(communicationGet(communication, local21)) & uint64(uint64(255)));
                        local23 = (uint64(communicationGet(communication, (local21 + uint64(uint64(1))))) & uint64(uint64(255)));
                        local24 = (uint64(communicationGet(communication, (local21 + uint64(uint64(2))))) & uint64(uint64(255)));
                        local25 = (uint64(communicationGet(communication, (local21 + uint64(uint64(3))))) & uint64(uint64(255)));
                        local26 = ((((local22 << uint64(uint64(24))) | (local23 << uint64(uint64(16)))) | (local24 << uint64(uint64(8)))) | local25);
                        for (uint64 binder1 = 0; binder1 < local10; binder1++) {
                            local37 = local37;
                            local27 = ((local13 * local10) + local37);
                            local28 = ((local14 * local10) + local37);
                            local29 = arrayGet(environment0, local28).item0;
                            if ((local37 < local20)) {
                                arraySet(environment0, local27, Tuple0(local29));
                            } else {
                                local30 = (local37 - local20);
                                local31 = ((local14 * local10) + local30);
                                local32 = arrayGet(environment0, local31).item0;
                                local33 = (local32 + local26);
                                if ((local29 < local33)) {
                                    arraySet(environment0, local27, Tuple0(local33));
                                } else {
                                    arraySet(environment0, local27, Tuple0(local29));
                                }
                            }
                        }
                    }
                    local34 = ((local3 * local10) + local9);
                    local35 = arrayGet(environment0, local34).item0;
                    if ((!(local0 < uint64(uint64(8))))) {
                        for (uint64 binder2 = 0; binder2 < uint64(8); binder2++) {
                            communicationSet(communication, local36, uint8(uint64(0)));
                        }
                        local38 = uint64(uint64(72057594037927936));
                        communicationSet(communication, uint64(0), uint8(divint64((local35), (local38))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(1), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(2), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(3), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(4), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(5), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        local38 = divint64((local38), (uint64(uint64(256))));
                        communicationSet(communication, uint64(6), uint8((divint64((local35), (local38)) % uint64(uint64(256)))));
                        communicationSet(communication, uint64(7), uint8((local35 % uint64(uint64(256)))));
                    } else {
                    }
                }
            }
        }
    } }

    fallback() external payable {
        bytes memory data = msg.data;
        procedure0(environment0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, data);
        assembly {
            return(add(data, 0x20), mload(data))
        }
    }
}
