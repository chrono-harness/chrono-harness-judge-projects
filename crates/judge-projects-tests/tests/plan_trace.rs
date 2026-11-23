use chrono_judge_projects::plan_trace::PlanTrace;
use std::collections::BTreeMap;
use std::sync::{Arc, Barrier, Mutex};
use tracing_subscriber::prelude::*;
use tracing_tunnel::TracingEvent;

#[test]
fn interleaved_workers_emit_their_own_operation_and_the_same_plan_parent() {
    let recorded = Arc::new(Mutex::new(Vec::new()));
    let copy = recorded.clone();
    let subscriber = tracing_subscriber::registry().with(PlanTrace(move |frame| {
        copy.lock().unwrap().push(frame);
    }));
    tracing::subscriber::with_default(subscriber, || {
        let plan = tracing::info_span!("plan", identity = "fixed");
        let _scope = plan.enter();
        let dispatch = tracing::dispatcher::get_default(Clone::clone);
        let ready = Barrier::new(2);
        std::thread::scope(|scope| {
            for name in ["first", "second"] {
                let (dispatch, parent, ready) = (&dispatch, tracing::Span::current(), &ready);
                scope.spawn(move || {
                    tracing::dispatcher::with_default(dispatch, || {
                        let _plan = parent.enter();
                        let operation = tracing::info_span!("worker", operation = name);
                        let _scope = operation.enter();
                        ready.wait();
                        tracing::info!(finished = name);
                    })
                });
            }
        });
    });
    let mut spans = BTreeMap::new();
    let mut observed = Vec::new();
    for frame in recorded.lock().unwrap().iter() {
        match frame {
            TracingEvent::NewSpan {
                id,
                parent_id,
                values,
                ..
            } => {
                spans.insert(*id, (*parent_id, serde_json::to_value(values).unwrap()));
            }
            TracingEvent::NewEvent { parent, values, .. } => {
                let (plan, fields) = &spans[&parent.unwrap()];
                let finished = serde_json::to_value(values).unwrap();
                assert_eq!(fields["operation"], finished["finished"]);
                assert_eq!(spans[&plan.unwrap()].1["identity"]["string"], "fixed");
                observed.push(finished["finished"]["string"].as_str().unwrap().to_owned());
            }
            _ => {}
        }
    }
    observed.sort();
    assert_eq!(observed, ["first", "second"]);
}
