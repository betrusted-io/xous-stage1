
pub struct KernelArguments {
    pub base: *const u32,
}

pub struct KernelArgumentsIterator {
    base: *const u32,
    size: u32,
    offset: u32,
}

impl KernelArguments {
    pub fn new(base: *const u32) -> Self {
        KernelArguments { base }
    }

    pub fn iter(&self) -> KernelArgumentsIterator {
        KernelArgumentsIterator { base: self.base, size: self.size(), offset: 0 }
    }

    pub fn size(&self) -> u32 {
        unsafe { self.base.add(2).read() * 4 as u32 }
    }
}

pub struct KernelArgument {
    pub name: u32,
    pub size: u32,
    pub data: &'static [u32],
}

impl KernelArgument {
    pub fn new(base: *const u32, offset: u32) -> Self {
        let name = unsafe { base.add(offset as usize / 4).read() };
        let size = unsafe { base.add(offset as usize / 4 + 1).read() };
        let data = unsafe { core::slice::from_raw_parts(base.add(offset as usize / 4 + 2), size as usize) };
        KernelArgument {
            name,
            size: size * 4,
            data,
        }
    }
}

impl Iterator for KernelArgumentsIterator {
    type Item = KernelArgument;
    fn next(&mut self) -> Option<Self::Item> {
        if self.offset > self.size {
            None
        } else {
            let new_arg = KernelArgument::new(self.base, self.offset);
            self.offset += new_arg.size;
            Some(new_arg)
        }
    }
}
