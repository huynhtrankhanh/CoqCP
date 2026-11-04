From Trusted Require Import Protocol CapacityGeneral CapacitySet.
Module Capacity.
Definition within_capacity (requests:list Protocol.request) := CapacityGeneral.domain requests \/ CapacitySet.domain requests.
End Capacity.
