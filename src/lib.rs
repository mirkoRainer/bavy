use std::{fmt, str::FromStr, sync::atomic::{AtomicUsize, Ordering}};

use tracing;

/// Describes the level of verbosity of a span or event.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Level(LevelInner);

/// A filter comparable to a verbosity `Level`.
///
/// If a `Level` is considered less than a `LevelFilter`, it should be
/// considered disabled; if greater than or equal to the `LevelFilter`, that
/// level is enabled.
///
/// Note that this is essentially identical to the `Level` type, but with the
/// addition of an `OFF` level that completely disables all trace
/// instrumentation.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct LevelFilter(Option<Level>);

/// Indicates that a string could not be parsed to a valid level.
#[derive(Clone, Debug)]
pub struct ParseLevelFilterError(());

static MAX_LEVEL: AtomicUsize = AtomicUsize::new(LevelFilter::OFF_USIZE);

// ===== impl Level =====

impl Level {
    /// The "error" level.
    ///
    /// Designates very serious errors.
    pub const ERROR: Level = Level(LevelInner::Error);
    /// The "warn" level.
    ///
    /// Designates hazardous situations.
    pub const WARN: Level = Level(LevelInner::Warn);
    /// The "bavy" level.
    ///
    /// Designates bavy information.
    pub const BAVY: Level = Level(LevelInner::Bavy);
    /// The "info" level.
    ///
    /// Designates useful information.
    pub const INFO: Level = Level(LevelInner::Info);
    /// The "debug" level.
    ///
    /// Designates lower priority information.
    pub const DEBUG: Level = Level(LevelInner::Debug);
    /// The "trace" level.
    ///
    /// Designates very low priority, often extremely verbose, information.
    pub const TRACE: Level = Level(LevelInner::Trace);
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Level::TRACE => f.pad("TRACE"),
            Level::DEBUG => f.pad("DEBUG"),
            Level::BAVY => f.pad("BAVY"),
            Level::INFO => f.pad("INFO"),
            Level::WARN => f.pad("WARN"),
            Level::ERROR => f.pad("ERROR"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl crate::stdlib::error::Error for ParseLevelError {}

impl FromStr for Level {
    type Err = ParseLevelError;
    fn from_str(s: &str) -> Result<Self, ParseLevelError> {
        s.parse::<usize>()
            .map_err(|_| ParseLevelError { _p: () })
            .and_then(|num| match num {
                1 => Ok(Level::ERROR),
                2 => Ok(Level::WARN),
                3 => Ok(Level::BAVY),
                4 => Ok(Level::INFO),
                5 => Ok(Level::DEBUG),
                6 => Ok(Level::TRACE),
                _ => Err(ParseLevelError { _p: () }),
            })
            .or_else(|_| match s {
                s if s.eq_ignore_ascii_case("error") => Ok(Level::ERROR),
                s if s.eq_ignore_ascii_case("warn") => Ok(Level::WARN),
                s if s.eq_ignore_ascii_case("bavy") => Ok(Level::BAVY),
                s if s.eq_ignore_ascii_case("info") => Ok(Level::INFO),
                s if s.eq_ignore_ascii_case("debug") => Ok(Level::DEBUG),
                s if s.eq_ignore_ascii_case("trace") => Ok(Level::TRACE),
                _ => Err(ParseLevelError { _p: () }),
            })
    }
}

#[repr(usize)]
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
enum LevelInner {
    /// The "trace" level.
    ///
    /// Designates very low priority, often extremely verbose, information.
    Trace = 0,
    /// The "debug" level.
    ///
    /// Designates lower priority information.
    Debug = 1,
    /// The "info" level.
    ///
    /// Designates useful information.
    Info = 2,
    /// The "bavy" level.
    ///
    /// Designates bavy information.
    Bavy = 3,
    /// The "warn" level.
    ///
    /// Designates hazardous situations.
    Warn = 4,
    /// The "error" level.
    ///
    /// Designates very serious errors.
    Error = 5,
}

// === impl LevelFilter ===

impl From<Level> for LevelFilter {
    #[inline]
    fn from(level: Level) -> Self {
        Self::from_level(level)
    }
}

impl From<Option<Level>> for LevelFilter {
    #[inline]
    fn from(level: Option<Level>) -> Self {
        Self(level)
    }
}

impl From<LevelFilter> for Option<Level> {
    #[inline]
    fn from(filter: LevelFilter) -> Self {
        filter.into_level()
    }
}

impl LevelFilter {
    /// The "off" level.
    ///
    /// Designates that trace instrumentation should be completely disabled.
    pub const OFF: LevelFilter = LevelFilter(None);
    /// The "error" level.
    ///
    /// Designates very serious errors.
    pub const ERROR: LevelFilter = LevelFilter::from_level(Level::ERROR);
    /// The "warn" level.
    ///
    /// Designates hazardous situations.
    pub const WARN: LevelFilter = LevelFilter::from_level(Level::WARN);
    /// The "bavy" level.
    ///
    /// Designates bavy information.
    pub const BAVY: LevelFilter = LevelFilter::from_level(Level::BAVY);
    /// The "info" level.
    ///
    /// Designates useful information.
    pub const INFO: LevelFilter = LevelFilter::from_level(Level::INFO);
    /// The "debug" level.
    ///
    /// Designates lower priority information.
    pub const DEBUG: LevelFilter = LevelFilter::from_level(Level::DEBUG);
    /// The "trace" level.
    ///
    /// Designates very low priority, often extremely verbose, information.
    pub const TRACE: LevelFilter = LevelFilter(Some(Level::TRACE));

    /// Returns a `LevelFilter` that enables spans and events with verbosity up
    /// to and including `level`.
    pub const fn from_level(level: Level) -> Self {
        Self(Some(level))
    }

    /// Returns the most verbose [`Level`] that this filter accepts, or `None`
    /// if it is [`OFF`].
    ///
    /// [`Level`]: ../struct.Level.html
    /// [`OFF`]: #associatedconstant.OFF
    pub const fn into_level(self) -> Option<Level> {
        self.0
    }

    // These consts are necessary because `as` casts are not allowed as
    // match patterns.
    const ERROR_USIZE: usize = LevelInner::Error as usize;
    const WARN_USIZE: usize = LevelInner::Warn as usize;
    const BAVY_USIZE: usize = LevelInner::Bavy as usize;
    const INFO_USIZE: usize = LevelInner::Info as usize;
    const DEBUG_USIZE: usize = LevelInner::Debug as usize;
    const TRACE_USIZE: usize = LevelInner::Trace as usize;
    // Using the value of the last variant + 1 ensures that we match the value
    // for `Option::None` as selected by the niche optimization for
    // `LevelFilter`. If this is the case, converting a `usize` value into a
    // `LevelFilter` (in `LevelFilter::current`) will be an identity conversion,
    // rather than generating a lookup table.
    const OFF_USIZE: usize = LevelInner::Error as usize + 1;

    /// Returns a `LevelFilter` that matches the most verbose [`Level`] that any
    /// currently active [`Subscriber`] will enable.
    ///
    /// User code should treat this as a *hint*. If a given span or event has a
    /// level *higher* than the returned `LevelFilter`, it will not be enabled.
    /// However, if the level is less than or equal to this value, the span or
    /// event is *not* guaranteed to be enabled; the subscriber will still
    /// filter each callsite individually.
    ///
    /// Therefore, comparing a given span or event's level to the returned
    /// `LevelFilter` **can** be used for determining if something is
    /// *disabled*, but **should not** be used for determining if something is
    /// *enabled*.`
    ///
    /// [`Level`]: ../struct.Level.html
    /// [`Subscriber`]: ../../trait.Subscriber.html
    #[inline(always)]
    pub fn current() -> Self {
        match MAX_LEVEL.load(Ordering::Relaxed) {
            Self::ERROR_USIZE => Self::ERROR,
            Self::WARN_USIZE => Self::WARN,
            Self::BAVY_USIZE => Self::BAVY,
            Self::INFO_USIZE => Self::INFO,
            Self::DEBUG_USIZE => Self::DEBUG,
            Self::TRACE_USIZE => Self::TRACE,
            Self::OFF_USIZE => Self::OFF,
            #[cfg(debug_assertions)]
            unknown => unreachable!(
                "/!\\ `LevelFilter` representation seems to have changed! /!\\ \n\
                This is a bug (and it's pretty bad). Please contact the `tracing` \
                maintainers. Thank you and I'm sorry.\n \
                The offending repr was: {:?}",
                unknown,
            ),
            #[cfg(not(debug_assertions))]
            _ => unsafe {
                // Using `unreachable_unchecked` here (rather than
                // `unreachable!()`) is necessary to ensure that rustc generates
                // an identity conversion from integer -> discriminant, rather
                // than generating a lookup table. We want to ensure this
                // function is a single `mov` instruction (on x86) if at all
                // possible, because it is called *every* time a span/event
                // callsite is hit; and it is (potentially) the only code in the
                // hottest path for skipping a majority of callsites when level
                // filtering is in use.
                //
                // safety: This branch is only truly unreachable if we guarantee
                // that no values other than the possible enum discriminants
                // will *ever* be present. The `AtomicUsize` is initialized to
                // the `OFF` value. It is only set by the `set_max` function,
                // which takes a `LevelFilter` as a parameter. This restricts
                // the inputs to `set_max` to the set of valid discriminants.
                // Therefore, **as long as `MAX_VALUE` is only ever set by
                // `set_max`**, this is safe.
                crate::stdlib::hint::unreachable_unchecked()
            },
        }
    }

    pub(crate) fn set_max(LevelFilter(level): LevelFilter) {
        let val = match level {
            Some(Level(level)) => level as usize,
            None => Self::OFF_USIZE,
        };

        // using an AcqRel swap ensures an ordered relationship of writes to the
        // max level.
        MAX_LEVEL.swap(val, Ordering::AcqRel);
    }
}

impl fmt::Display for LevelFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            LevelFilter::OFF => f.pad("off"),
            LevelFilter::ERROR => f.pad("error"),
            LevelFilter::WARN => f.pad("warn"),
            LevelFilter::BAVY => f.pad("bavy"),
            LevelFilter::INFO => f.pad("info"),
            LevelFilter::DEBUG => f.pad("debug"),
            LevelFilter::TRACE => f.pad("trace"),
        }
    }
}

impl fmt::Debug for LevelFilter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            LevelFilter::OFF => f.pad("LevelFilter::OFF"),
            LevelFilter::ERROR => f.pad("LevelFilter::ERROR"),
            LevelFilter::WARN => f.pad("LevelFilter::WARN"),
            LevelFilter::BAVY => f.pad("LevelFilter::BAVY"),
            LevelFilter::INFO => f.pad("LevelFilter::INFO"),
            LevelFilter::DEBUG => f.pad("LevelFilter::DEBUG"),
            LevelFilter::TRACE => f.pad("LevelFilter::TRACE"),
        }
    }
}

impl FromStr for LevelFilter {
    type Err = ParseLevelFilterError;
    fn from_str(from: &str) -> Result<Self, Self::Err> {
        from.parse::<usize>()
            .ok()
            .and_then(|num| match num {
                0 => Some(LevelFilter::OFF),
                1 => Some(LevelFilter::ERROR),
                2 => Some(LevelFilter::WARN),
                3 => Some(LevelFilter::BAVY),
                4 => Some(LevelFilter::INFO),
                5 => Some(LevelFilter::DEBUG),
                6 => Some(LevelFilter::TRACE),
                _ => None,
            })
            .or_else(|| match from {
                "" => Some(LevelFilter::ERROR),
                s if s.eq_ignore_ascii_case("error") => Some(LevelFilter::ERROR),
                s if s.eq_ignore_ascii_case("warn") => Some(LevelFilter::WARN),
                s if s.eq_ignore_ascii_case("bavy") => Some(LevelFilter::BAVY),
                s if s.eq_ignore_ascii_case("info") => Some(LevelFilter::INFO),
                s if s.eq_ignore_ascii_case("debug") => Some(LevelFilter::DEBUG),
                s if s.eq_ignore_ascii_case("trace") => Some(LevelFilter::TRACE),
                s if s.eq_ignore_ascii_case("off") => Some(LevelFilter::OFF),
                _ => None,
            })
            .ok_or(ParseLevelFilterError(()))
    }
}

/// Returned if parsing a `Level` fails.
#[derive(Debug)]
pub struct ParseLevelError {
    _p: (),
}

impl fmt::Display for ParseLevelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad(
            "error parsing level: expected one of \"error\", \"warn\", \
            \"bavy\", k\"info\", \"debug\", \"trace\", or a number 1-5",
        )
    }
}

impl fmt::Display for ParseLevelFilterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad(
            "error parsing level filter: expected one of \"off\", \"error\", \
            \"warn\", \"bavy\", \"info\", \"debug\", \"trace\", or a number 0-5",
        )
    }
}


#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn level_from_str() {
        assert_eq!("error".parse::<Level>().unwrap(), Level::ERROR);
        assert_eq!("5".parse::<Level>().unwrap(), Level::DEBUG);
        assert_eq!("4".parse::<Level>().unwrap(), Level::INFO);
        assert_eq!("3".parse::<Level>().unwrap(), Level::BAVY);
        assert!("0".parse::<Level>().is_err())
    }

    #[test]
    fn filter_level_conversion() {
        let mapping = [
            (LevelFilter::OFF, None),
            (LevelFilter::ERROR, Some(Level::ERROR)),
            (LevelFilter::WARN, Some(Level::WARN)),
            (LevelFilter::INFO, Some(Level::INFO)),
            (LevelFilter::DEBUG, Some(Level::DEBUG)),
            (LevelFilter::TRACE, Some(Level::TRACE)),
        ];
        for (filter, level) in mapping.iter() {
            assert_eq!(filter.clone().into_level(), *level);
            match level {
                Some(level) => {
                    let actual: LevelFilter = level.clone().into();
                    assert_eq!(actual, *filter);
                }
                None => {
                    let actual: LevelFilter = None.into();
                    assert_eq!(actual, *filter);
                }
            }
        }
    }

    #[test]
    fn level_filter_is_usize_sized() {
        assert_eq!(
            mem::size_of::<LevelFilter>(),
            mem::size_of::<usize>(),
            "`LevelFilter` is no longer `usize`-sized! global MAX_LEVEL may now be invalid!"
        )
    }

    #[test]
    fn level_filter_reprs() {
        let mapping = [
            (LevelFilter::OFF, LevelInner::Error as usize + 1),
            (LevelFilter::ERROR, LevelInner::Error as usize),
            (LevelFilter::WARN, LevelInner::Warn as usize),
            (LevelFilter::INFO, LevelInner::Info as usize),
            (LevelFilter::DEBUG, LevelInner::Debug as usize),
            (LevelFilter::TRACE, LevelInner::Trace as usize),
        ];
        for &(filter, expected) in &mapping {
            let repr = unsafe {
                // safety: The entire purpose of this test is to assert that the
                // actual repr matches what we expect it to be --- we're testing
                // that *other* unsafe code is sound using the transmuted value.
                // We're not going to do anything with it that might be unsound.
                mem::transmute::<LevelFilter, usize>(filter)
            };
            assert_eq!(expected, repr, "repr changed for {:?}", filter)
        }
    }
}