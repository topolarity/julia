# This file is a part of Julia. License is MIT: https://julialang.org/license

import Base: AbstractTime, Period, Instant, UTInstant, TimeType, AbstractDateTime
import Base: DatePeriod, Year, Quarter, Month, Week, Day
import Base: TimePeriod, Hour, Minute, Second, Millisecond, Microsecond, Nanosecond
import Base: DateTime, Date, Time, validargs, isleapyear, daysinmonth
import Base: AMPM, AM, PM, TWENTYFOURHOUR, UTM, UTD

# Calendar types provide rules for interpreting instant
# timelines in human-readable form.
abstract type Calendar <: AbstractTime end

# ISOCalendar implements the ISO 8601 standard (en.wikipedia.org/wiki/ISO_8601)
# Notably based on the proleptic Gregorian calendar
# ISOCalendar provides interpretation rules for UTInstants to civil date and time parts
struct ISOCalendar <: Calendar end

"""
    TimeZone

Geographic zone generally based on longitude determining what the time is at a certain location.
Some time zones observe daylight savings (eg EST -> EDT).
For implementations and more support, see the [`TimeZones.jl`](https://github.com/JuliaTime/TimeZones.jl) package
"""
abstract type TimeZone end

"""
    UTC

`UTC`, or Coordinated Universal Time, is the [`TimeZone`](@ref) from which all others are measured.
It is associated with the time at 0° longitude. It is not adjusted for daylight savings.
"""
struct UTC <: TimeZone end

### CONSTRUCTORS ###
# Convenience constructors from Periods
function DateTime(y::Year, m::Month=Month(1), d::Day=Day(1),
                  h::Hour=Hour(0), mi::Minute=Minute(0),
                  s::Second=Second(0), ms::Millisecond=Millisecond(0))
    return DateTime(value(y), value(m), value(d),
                    value(h), value(mi), value(s), value(ms))
end

Date(y::Year, m::Month=Month(1), d::Day=Day(1)) = Date(value(y), value(m), value(d))

function Time(h::Hour, mi::Minute=Minute(0), s::Second=Second(0),
              ms::Millisecond=Millisecond(0),
              us::Microsecond=Microsecond(0), ns::Nanosecond=Nanosecond(0))
    return Time(value(h), value(mi), value(s), value(ms), value(us), value(ns))
end

# To allow any order/combination of Periods

"""
    DateTime(periods::Period...) -> DateTime

Construct a `DateTime` type by `Period` type parts. Arguments may be in any order. DateTime
parts not provided will default to the value of `Dates.default(period)`.
"""
function DateTime(period::Period, periods::Period...)
    y = Year(1); m = Month(1); d = Day(1)
    h = Hour(0); mi = Minute(0); s = Second(0); ms = Millisecond(0)
    for p in (period, periods...)
        isa(p, Year) && (y = p::Year)
        isa(p, Month) && (m = p::Month)
        isa(p, Day) && (d = p::Day)
        isa(p, Hour) && (h = p::Hour)
        isa(p, Minute) && (mi = p::Minute)
        isa(p, Second) && (s = p::Second)
        isa(p, Millisecond) && (ms = p::Millisecond)
    end
    return DateTime(y, m, d, h, mi, s, ms)
end

"""
    Date(period::Period...) -> Date

Construct a `Date` type by `Period` type parts. Arguments may be in any order. `Date` parts
not provided will default to the value of `Dates.default(period)`.
"""
function Date(period::Period, periods::Period...)
    y = Year(1); m = Month(1); d = Day(1)
    for p in (period, periods...)
        isa(p, Year) && (y = p::Year)
        isa(p, Month) && (m = p::Month)
        isa(p, Day) && (d = p::Day)
    end
    return Date(y, m, d)
end

"""
    Time(period::TimePeriod...) -> Time

Construct a `Time` type by `Period` type parts. Arguments may be in any order. `Time` parts
not provided will default to the value of `Dates.default(period)`.
"""
function Time(period::TimePeriod, periods::TimePeriod...)
    h = Hour(0); mi = Minute(0); s = Second(0)
    ms = Millisecond(0); us = Microsecond(0); ns = Nanosecond(0)
    for p in (period, periods...)
        isa(p, Hour) && (h = p::Hour)
        isa(p, Minute) && (mi = p::Minute)
        isa(p, Second) && (s = p::Second)
        isa(p, Millisecond) && (ms = p::Millisecond)
        isa(p, Microsecond) && (us = p::Microsecond)
        isa(p, Nanosecond) && (ns = p::Nanosecond)
    end
    return Time(h, mi, s, ms, us, ns)
end

# Convenience constructor for DateTime from Date and Time
"""
    DateTime(d::Date, t::Time)

Construct a `DateTime` type by `Date` and `Time`.
Non-zero microseconds or nanoseconds in the `Time` type will result in an
`InexactError`.

!!! compat "Julia 1.1"
    This function requires at least Julia 1.1.

```jldoctest
julia> d = Date(2018, 1, 1)
2018-01-01

julia> t = Time(8, 15, 42)
08:15:42

julia> DateTime(d, t)
2018-01-01T08:15:42
```
"""
function DateTime(dt::Date, t::Time)
    (microsecond(t) > 0 || nanosecond(t) > 0) && throw(InexactError(:DateTime, DateTime, t))
    y, m, d = yearmonthday(dt)
    return DateTime(y, m, d, hour(t), minute(t), second(t), millisecond(t))
end

# Traits, Equality
Base.isfinite(::Union{Type{T}, T}) where {T<:TimeType} = true
calendar(dt::DateTime) = ISOCalendar
calendar(dt::Date) = ISOCalendar

"""
    eps(::Type{DateTime}) -> Millisecond
    eps(::Type{Date}) -> Day
    eps(::Type{Time}) -> Nanosecond
    eps(::TimeType) -> Period

Return the smallest unit value supported by the `TimeType`.

# Examples
```jldoctest
julia> eps(DateTime)
1 millisecond

julia> eps(Date)
1 day

julia> eps(Time)
1 nanosecond
```
"""
Base.eps(::Union{Type{DateTime}, Type{Date}, Type{Time}, TimeType})

Base.eps(::Type{DateTime}) = Millisecond(1)
Base.eps(::Type{Date}) = Day(1)
Base.eps(::Type{Time}) = Nanosecond(1)
Base.eps(::T) where T <: TimeType = eps(T)::Period

# zero returns dt::T - dt::T
Base.zero(::Type{DateTime}) = Millisecond(0)
Base.zero(::Type{Date}) = Day(0)
Base.zero(::Type{Time}) = Nanosecond(0)
Base.zero(::T) where T <: TimeType = zero(T)::Period


Base.typemax(::Union{DateTime, Type{DateTime}}) = DateTime(146138512, 12, 31, 23, 59, 59)
Base.typemin(::Union{DateTime, Type{DateTime}}) = DateTime(-146138511, 1, 1, 0, 0, 0)
Base.typemax(::Union{Date, Type{Date}}) = Date(252522163911149, 12, 31)
Base.typemin(::Union{Date, Type{Date}}) = Date(-252522163911150, 1, 1)
Base.typemax(::Union{Time, Type{Time}}) = Time(23, 59, 59, 999, 999, 999)
Base.typemin(::Union{Time, Type{Time}}) = Time(0)
# Date-DateTime promotion, isless, ==
Base.promote_rule(::Type{Date}, x::Type{DateTime}) = DateTime
Base.isless(x::T, y::T) where {T<:TimeType} = isless(value(x), value(y))
Base.isless(x::TimeType, y::TimeType) = isless(promote(x, y)...)
(==)(x::T, y::T) where {T<:TimeType} = (==)(value(x), value(y))
(==)(x::TimeType, y::TimeType) = (===)(promote(x, y)...)
Base.min(x::AbstractTime) = x
Base.max(x::AbstractTime) = x
Base.minmax(x::AbstractTime) = (x, x)
Base.hash(x::Time, h::UInt) =
    hash(hour(x), hash(minute(x), hash(second(x),
        hash(millisecond(x), hash(microsecond(x), hash(nanosecond(x), h))))))

Base.sleep(duration::Period) = sleep(seconds(duration))

function Base.Timer(delay::Period; interval::Period=Second(0))
    Timer(seconds(delay), interval=seconds(interval))
end

function Base.timedwait(testcb, timeout::Period; pollint::Period=Millisecond(100))
    timedwait(testcb, seconds(timeout), pollint=seconds(pollint))
end

Base.OrderStyle(::Type{<:AbstractTime}) = Base.Ordered()
Base.ArithmeticStyle(::Type{<:AbstractTime}) = Base.ArithmeticWraps()
