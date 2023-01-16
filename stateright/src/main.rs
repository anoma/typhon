pub mod acceptor_state;
pub mod message;
pub mod proto;

use stateright::report::WriteReporter;
use stateright::{Checker, Model, Property};
use std::hash::Hash;

use crate::acceptor_state::AcceptorState;

#[derive(Clone)]
struct TwoPhaseSys {}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TwoPhaseState {}

// #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
// enum Message {}

#[derive(Clone, Debug)]
enum Action {}

impl Model for TwoPhaseSys {
    type State = TwoPhaseState;
    type Action = Action;

    fn init_states(&self) -> Vec<Self::State> {
        vec![]
    }

    fn actions(&self, _state: &Self::State, _actions: &mut Vec<Self::Action>) {}

    fn next_state(&self, last_state: &Self::State, _action: Self::Action) -> Option<Self::State> {
        let state = last_state.clone();
        Some(state)
    }

    fn properties(&self) -> Vec<Property<Self>> {
        vec![]
    }
}

fn main() -> Result<(), pico_args::Error> {
    env_logger::init_from_env(env_logger::Env::default().default_filter_or("info")); // `RUST_LOG=${LEVEL}` env variable to override

    let mut args = pico_args::Arguments::from_env();
    match args.subcommand()?.as_deref() {
        Some("check") => {
            let rm_count = args.opt_free_from_str()?.unwrap_or(2);
            println!("Checking hpaxos with {} acceptors.", rm_count);
            TwoPhaseSys {}
                .checker()
                .threads(num_cpus::get())
                .spawn_dfs()
                .report(&mut WriteReporter::new(&mut std::io::stdout()));
        }
        _ => {
            println!("USAGE:");
            println!("  ./hpaxos check [RESOURCE_MANAGER_COUNT]");
        }
    }

    Ok(())
}
