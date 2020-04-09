// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for loading the device tree.

use vm_memory::{ByteValued, Bytes, GuestMemory};

use std::error::Error as StdError;
use std::fmt;

use crate::configurator::{BootConfigurator, BootParams, Error as BootConfiguratorError, Result};

/// Errors specific to the device tree boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Error writing FDT in memory.
    WriteFDTToMemory,
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            WriteFDTToMemory => "Error writing FDT in guest memory.",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Device Tree Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

impl From<Error> for BootConfiguratorError {
    fn from(err: Error) -> Self {
        BootConfiguratorError::Fdt(err)
    }
}

/// Boot configurator for device tree.
pub struct FdtBootConfigurator {}

impl BootConfigurator for FdtBootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// # Arguments
    ///
    /// * `params` - boot parameters containing the FDT.
    /// * `guest_memory` - guest's physical memory.
    fn write_bootparams<T, S, R, M>(params: BootParams<T, S, R>, guest_memory: &M) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        R: ByteValued,
        M: GuestMemory,
    {
        // The VMM has filled an FDT and passed it as a `ByteValued` object.
        guest_memory
            .write_obj(params.header.header, params.header.address)
            .map_err(|_| Error::WriteFDTToMemory.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loader::tests::MEM_SIZE;
    use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

    // Maximum size of the device tree blob.
    const FDT_MAX_SIZE: usize = 0x20_0000;
    // Start of RAM on 64 bit ARM.
    const DRAM_MEM_START: u64 = 0x8000_0000; // 2 GB.

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    #[derive(Clone, Copy, Default)]
    struct FdtPlaceholder {
        content: Vec<u8>,
    }
    unsafe impl ByteValued for FdtPlaceholder {}

    #[test]
    fn test_configure_fdt_boot() {
        let mut fdt = FdtPlaceholder {
            content: vec![0u8; FDT_MAX_SIZE + 1],
        };
        let guest_memory = create_guest_mem();

        let mut fdt_addr = GuestAddress(DRAM_MEM_START);
        if let Some(addr) = guest_memory
            .last_addr()
            .checked_sub(FDT_MAX_SIZE as u64 - 1)
        {
            if guest_memory.address_in_range(addr) {
                fdt_addr = addr;
            }
        }

        // Error case: FDT doesn't fit in guest memory.
        eprintln!(
            "{}",
            FdtBootConfigurator::write_bootparams::<
                FdtPlaceholder,
                FdtPlaceholder,
                FdtPlaceholder,
                GuestMemoryMmap,
            >(BootParams::new(fdt, fdt_addr, None, None), &guest_memory,)
        );
        //            .is_ok());

        assert!(FdtBootConfigurator::write_bootparams::<
            FdtPlaceholder,
            FdtPlaceholder,
            FdtPlaceholder,
            GuestMemoryMmap,
        >(BootParams::new(fdt, fdt_addr, None, None), &guest_memory,)
        .is_ok());
    }
}
