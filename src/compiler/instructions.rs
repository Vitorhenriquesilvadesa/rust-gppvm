#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    Halt = 0,
    Ret,
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Dot,
    MatMul,
    MatTranspose,
    MatInversion,
    LShift,
    RShift,
    BitAnd,
    BitOr,
    BitNot,
    BitXor,
    And,
    Or,
    Not,
    Push,
    Pop,
    Swap,
    Dup,
    InvokeVirtual,
    InvokeNative,
    Cmp,
    Eq,
    Neq,
    GreaterThan,
    LessThan,
    GreaterEqual,
    LessEqual,
    Sync,
    CopyToDevice,
    CopyToHost,
    SpawnKernel,
    TupleGet,
    ListGet,
    ListSet,
    Load,
    Store,
    Get,
    Set,
    Jump,
    JLF,
    JFalse,
    Raise,
    CatchError,
    True,
    False,
    Constant,
}

impl From<Instruction> for u8 {
    fn from(instr: Instruction) -> u8 {
        instr as u8
    }
}

impl TryFrom<u8> for Instruction {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Instruction::Halt),
            1 => Ok(Instruction::Ret),
            2 => Ok(Instruction::Add),
            3 => Ok(Instruction::Sub),
            4 => Ok(Instruction::Mul),
            5 => Ok(Instruction::Div),
            6 => Ok(Instruction::Pow),
            7 => Ok(Instruction::Dot),
            8 => Ok(Instruction::MatMul),
            9 => Ok(Instruction::MatTranspose),
            10 => Ok(Instruction::MatInversion),
            11 => Ok(Instruction::LShift),
            12 => Ok(Instruction::RShift),
            13 => Ok(Instruction::BitAnd),
            14 => Ok(Instruction::BitOr),
            15 => Ok(Instruction::BitNot),
            16 => Ok(Instruction::BitXor),
            17 => Ok(Instruction::And),
            18 => Ok(Instruction::Or),
            19 => Ok(Instruction::Not),
            20 => Ok(Instruction::Push),
            21 => Ok(Instruction::Pop),
            22 => Ok(Instruction::Swap),
            23 => Ok(Instruction::Dup),
            24 => Ok(Instruction::InvokeVirtual),
            25 => Ok(Instruction::InvokeNative),
            26 => Ok(Instruction::Cmp),
            27 => Ok(Instruction::Eq),
            28 => Ok(Instruction::Neq),
            29 => Ok(Instruction::GreaterThan),
            30 => Ok(Instruction::LessThan),
            31 => Ok(Instruction::GreaterEqual),
            32 => Ok(Instruction::LessEqual),
            33 => Ok(Instruction::Sync),
            34 => Ok(Instruction::CopyToDevice),
            35 => Ok(Instruction::CopyToHost),
            36 => Ok(Instruction::SpawnKernel),
            37 => Ok(Instruction::TupleGet),
            38 => Ok(Instruction::ListGet),
            39 => Ok(Instruction::ListSet),
            40 => Ok(Instruction::Load),
            41 => Ok(Instruction::Store),
            42 => Ok(Instruction::Get),
            43 => Ok(Instruction::Set),
            44 => Ok(Instruction::Jump),
            45 => Ok(Instruction::JLF),
            46 => Ok(Instruction::JFalse),
            47 => Ok(Instruction::Raise),
            48 => Ok(Instruction::CatchError),
            49 => Ok(Instruction::Constant),
            _ => Err("Invalid instruction value."),
        }
    }
}
