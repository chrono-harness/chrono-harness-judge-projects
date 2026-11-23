//! Emit tracing-tunnel records with each worker's parent resolved before transport.
use tracing::{
    Event, Metadata, Subscriber,
    span::{Attributes, Id, Record},
    subscriber::Interest,
};
use tracing_subscriber::{Layer, layer::Context, registry::LookupSpan};
use tracing_tunnel::{TracedValues, TracingEvent};

pub struct PlanTrace<F>(pub F);

fn metadata_id(metadata: &'static Metadata<'static>) -> u64 {
    metadata as *const _ as usize as u64
}

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
