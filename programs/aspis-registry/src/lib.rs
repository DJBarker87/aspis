//! Governed mutation program for canonical Pool V1 verifier registries.
//!
//! There is no static program id: every registry and entry PDA is derived
//! from the runtime `program_id`. Governance authority is an exact signer
//! address and may therefore be a multisig PDA signing through CPI.

#![no_std]
#![allow(unexpected_cfgs)]

#[cfg(test)]
extern crate std;

pub mod error;
pub mod instruction;
mod processor;

pub use error::RegistryProgramErrorV1;
pub use instruction::{
    decode_registry_instruction, decode_registry_instruction_v1, decode_registry_instruction_v2,
    encode_initialize_registry_v1, encode_initialize_registry_v2, encode_schedule_profile_v1,
    encode_schedule_profile_v2, encode_simple_mutation_v1, encode_simple_mutation_v2,
    DecodedRegistryInstruction, RegistryInstructionV1, RegistryInstructionV2,
    RegistryMutationOpcodeV1, REGISTRY_INITIALIZE_INSTRUCTION_BYTES,
    REGISTRY_INITIALIZE_V2_INSTRUCTION_BYTES, REGISTRY_MUTATION_INSTRUCTION_MAGIC,
    REGISTRY_MUTATION_INSTRUCTION_VERSION, REGISTRY_MUTATION_INSTRUCTION_VERSION_V2,
    REGISTRY_SCHEDULE_INSTRUCTION_BYTES, REGISTRY_SCHEDULE_V2_INSTRUCTION_BYTES,
    REGISTRY_SIMPLE_MUTATION_INSTRUCTION_BYTES,
};
pub use processor::{
    pool_v1_verifier_entry_address, pool_v1_verifier_entry_v2_address,
    pool_v1_verifier_registry_address, pool_v1_verifier_registry_v2_address, process_instruction,
    POOL_V1_VERIFIER_ENTRY_SEED, POOL_V1_VERIFIER_ENTRY_V2_SEED, POOL_V1_VERIFIER_REGISTRY_SEED,
    POOL_V1_VERIFIER_REGISTRY_V2_SEED,
};
