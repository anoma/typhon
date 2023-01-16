fn main() {
    tonic_build::configure()
        .out_dir("src/proto/")
        .format(true)
        .compile(&["proto/hpaxosmessage.proto"], &["proto"])
        .unwrap();
}
