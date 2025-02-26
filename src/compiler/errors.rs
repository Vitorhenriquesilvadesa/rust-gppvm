#[macro_export]
macro_rules! gpp_error {
    ($($arg:tt)*) => {
        {
            eprintln!("Error: {}", format_args!($($arg)*));
            std::process::exit(1);
        }
    };
}
