//! Emit tracing-tunnel records with each worker's parent resolved before transport.
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// After the first failed frame, keep its error and skip every later write.
pub fn publish_frame<E, F: FnOnce() -> Option<E>>(first_error: &mut Option<E>, write: F)
    requires old(first_error).is_none() ==> write.requires(()),
    ensures
        old(first_error).is_some() ==> *first_error == *old(first_error),
        old(first_error).is_none() ==> write.ensures((), *first_error),
{
    if first_error.is_none() {
        *first_error = write();
    }
}
}

#[cfg(not(verus_keep_ghost))]
use tracing::{
    Event, Metadata, Subscriber,
    span::{Attributes, Id, Record},
    subscriber::Interest,
};
#[cfg(not(verus_keep_ghost))]
use tracing_subscriber::{Layer, layer::Context, registry::LookupSpan};
#[cfg(not(verus_keep_ghost))]
use tracing_tunnel::{TracedValues, TracingEvent};

#[cfg(not(verus_keep_ghost))]
pub struct PlanTrace<F>(pub F);

#[cfg(not(verus_keep_ghost))]
pub(crate) fn write_frame(event: &TracingEvent) -> std::io::Result<()> {
    use std::io::Write;
    let mut dest = std::io::stderr().lock();
    dest.write_all(b"chrono-trace-v1 ")?;
    serde_json::to_writer(&mut dest, event)?;
    dest.write_all(b"\n")?;
    dest.flush()
}

#[cfg(not(verus_keep_ghost))]
fn metadata_id(metadata: &'static Metadata<'static>) -> u64 {
    metadata as *const _ as usize as u64
}

#[cfg(not(verus_keep_ghost))]
impl<S, F> Layer<S> for PlanTrace<F>
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    F: Fn(TracingEvent) + Send + Sync + 'static,
{
    fn register_callsite(&self, metadata: &'static Metadata<'static>) -> Interest {
        (self.0)(TracingEvent::NewCallSite {
            id: metadata_id(metadata),
            data: metadata.into(),
        });
        Interest::always()
    }

    fn on_new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let span = ctx
            .span(id)
            .expect("span registered before layer notification");
        (self.0)(TracingEvent::NewSpan {
            id: id.into_u64(),
            parent_id: span.parent().map(|parent| parent.id().into_u64()),
            metadata_id: metadata_id(attrs.metadata()),
            values: TracedValues::from_values(attrs.values()),
        });
    }

    fn on_record(&self, id: &Id, values: &Record<'_>, _: Context<'_, S>) {
        (self.0)(TracingEvent::ValuesRecorded {
            id: id.into_u64(),
            values: TracedValues::from_record(values),
        });
    }

    fn on_follows_from(&self, id: &Id, follows: &Id, _: Context<'_, S>) {
        (self.0)(TracingEvent::FollowsFrom {
            id: id.into_u64(),
            follows_from: follows.into_u64(),
        });
    }

    fn on_event(&self, event: &Event<'_>, ctx: Context<'_, S>) {
        (self.0)(TracingEvent::NewEvent {
            metadata_id: metadata_id(event.metadata()),
            parent: ctx.event_span(event).map(|span| span.id().into_u64()),
            values: TracedValues::from_event(event),
        });
    }

    fn on_close(&self, id: Id, _: Context<'_, S>) {
        (self.0)(TracingEvent::SpanDropped { id: id.into_u64() });
    }
}
