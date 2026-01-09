mod init;

synstructure::decl_derive! {
    [InitPin] =>
    init::derive_init_pin
}

synstructure::decl_derive! {
    [Init] =>
    init::derive_init
}
