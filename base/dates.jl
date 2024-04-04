# This file is a part of Julia. License is MIT: https://julialang.org/license

abstract type AbstractTime end

"""
    Period
    Year
    Quarter
    Month
    Week
    Day
    Hour
    Minute
    Second
    Millisecond
    Microsecond
    Nanosecond

`Period` types represent discrete, human representations of time.
"""
abstract type Period     <: AbstractTime end

"""
    DatePeriod
    Year
    Quarter
    Month
    Week
    Day

Intervals of time greater than or equal to a day.
Conventional comparisons between `DatePeriod`s are not all valid.
(eg `Week(1) == Day(7)`, but `Year(1) != Day(365)`)
"""
abstract type DatePeriod <: Period end

"""
    TimePeriod
    Hour
    Minute
    Second
    Millisecond
    Microsecond
    Nanosecond

Intervals of time less than a day.
Conversions between all `TimePeriod`s are permissible.
(eg `Hour(1) == Minute(60) == Second(3600)`)
"""
abstract type TimePeriod <: Period end

for T in (:Year, :Quarter, :Month, :Week, :Day)
    @eval struct $T <: DatePeriod
        value::Int64
        $T(v::Number) = new(v)
    end
end
for T in (:Hour, :Minute, :Second, :Millisecond, :Microsecond, :Nanosecond)
    @eval struct $T <: TimePeriod
        value::Int64
        $T(v::Number) = new(v)
    end
end

"""
    Year(v)
    Quarter(v)
    Month(v)
    Week(v)
    Day(v)
    Hour(v)
    Minute(v)
    Second(v)
    Millisecond(v)
    Microsecond(v)
    Nanosecond(v)

Construct a `Period` type with the given `v` value. Input must be losslessly convertible
to an [`Int64`](@ref).
"""
Period(v)

"""
    Instant

`Instant` types represent integer-based, machine representations of time as continuous
timelines starting from an epoch.
"""
abstract type Instant <: AbstractTime end

"""
    UTInstant{T}

The `UTInstant` represents a machine timeline based on UT time (1 day = one revolution of
the earth). The `T` is a `Period` parameter that indicates the resolution or precision of
the instant.
"""
struct UTInstant{P<:Period} <: Instant
    periods::P
end

# Convenience default constructors
UTM(x) = UTInstant(Millisecond(x))
UTD(x) = UTInstant(Day(x))

"""
    TimeType

`TimeType` types wrap `Instant` machine instances to provide human representations of the
machine instant. `Time`, `DateTime` and `Date` are subtypes of `TimeType`.
"""
abstract type TimeType <: AbstractTime end

abstract type AbstractDateTime <: TimeType end

"""
    DateTime

`DateTime` represents a point in time according to the proleptic Gregorian calendar.
The finest resolution of the time is millisecond (i.e., microseconds or
nanoseconds cannot be represented by this type). The type supports fixed-point
arithmetic, and thus is prone to underflowing (and overflowing). A notable
consequence is rounding when adding a `Microsecond` or a `Nanosecond`:

```jldoctest
julia> dt = DateTime(2023, 8, 19, 17, 45, 32, 900)
2023-08-19T17:45:32.900

julia> dt + Millisecond(1)
2023-08-19T17:45:32.901

julia> dt + Microsecond(1000) # 1000us == 1ms
2023-08-19T17:45:32.901

julia> dt + Microsecond(999) # 999us rounded to 1000us
2023-08-19T17:45:32.901

julia> dt + Microsecond(1499) # 1499 rounded to 1000us
2023-08-19T17:45:32.901
```
"""
struct DateTime <: AbstractDateTime
    instant::UTInstant{Millisecond}
    DateTime(instant::UTInstant{Millisecond}) = new(instant)
end

"""
    Date

`Date` wraps a `UTInstant{Day}` and interprets it according to the proleptic Gregorian calendar.
"""
struct Date <: TimeType
    instant::UTInstant{Day}
    Date(instant::UTInstant{Day}) = new(instant)
end

"""
    Time

`Time` wraps a `Nanosecond` and represents a specific moment in a 24-hour day.
"""
struct Time <: TimeType
    instant::Nanosecond
    Time(instant::Nanosecond) = new(mod(instant, 86400000000000))
end


# Convert y,m,d to # of Rata Die days
# Works by shifting the beginning of the year to March 1,
# so a leap day is the very last day of the year
const SHIFTEDMONTHDAYS = (306, 337, 0, 31, 61, 92, 122, 153, 184, 214, 245, 275)
function totaldays(y, m, d)
    # If we're in Jan/Feb, shift the given year back one
    z = m < 3 ? y - 1 : y
    mdays = SHIFTEDMONTHDAYS[m]
    # days + month_days + year_days
    return d + mdays + 365z + fld(z, 4) - fld(z, 100) + fld(z, 400) - 306
end

# If the year is divisible by 4, except for every 100 years, except for every 400 years
isleapyear(y) = (y % 4 == 0) && ((y % 100 != 0) || (y % 400 == 0))

# Number of days in month
const DAYSINMONTH = (31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31)
daysinmonth(y,m) = DAYSINMONTH[m] + (m == 2 && isleapyear(y))

### UTILITIES ###

# These are necessary because the type constructors for TimeType subtypes can
# throw, and we want to be able to use tryparse without requiring a try/catch.
# This is made easier by providing a helper function that checks arguments, so
# we can validate arguments in tryparse.

"""
    validargs(::Type{<:TimeType}, args...) -> Union{ArgumentError, Nothing}

Determine whether the given arguments constitute valid inputs for the given type.
Returns either an `ArgumentError`, or [`nothing`](@ref) in case of success.
"""
function validargs end

# Julia uses 24-hour clocks internally, but user input can be AM/PM with 12pm == noon and 12am == midnight.
@enum AMPM AM PM TWENTYFOURHOUR
function adjusthour(h::Int64, ampm::AMPM)
    ampm == TWENTYFOURHOUR && return h
    ampm == PM && h < 12 && return h + 12
    ampm == AM && h == 12 && return Int64(0)
    return h
end

### CONSTRUCTORS ###

# Core constructors
"""
    DateTime(y, [m, d, h, mi, s, ms]) -> DateTime

Construct a `DateTime` type by parts. Arguments must be convertible to [`Int64`](@ref).
"""
function DateTime(y::Int64, m::Int64=1, d::Int64=1,
                  h::Int64=0, mi::Int64=0, s::Int64=0, ms::Int64=0, ampm::AMPM=TWENTYFOURHOUR)
    err = validargs(DateTime, y, m, d, h, mi, s, ms, ampm)
    err === nothing || throw(err)
    h = adjusthour(h, ampm)
    rata = ms + 1000 * (s + 60mi + 3600h + 86400 * totaldays(y, m, d))
    return DateTime(UTM(rata))
end

function validargs(::Type{DateTime}, y::Int64, m::Int64, d::Int64,
                   h::Int64, mi::Int64, s::Int64, ms::Int64, ampm::AMPM=TWENTYFOURHOUR)
    0 < m < 13 || return ArgumentError("Month: $m out of range (1:12)")
    0 < d < daysinmonth(y, m) + 1 || return ArgumentError("Day: $d out of range (1:$(daysinmonth(y, m)))")
    if ampm == TWENTYFOURHOUR # 24-hour clock
        -1 < h < 24 || (h == 24 && mi==s==ms==0) ||
            return ArgumentError("Hour: $h out of range (0:23)")
    else
        0 < h < 13 || return ArgumentError("Hour: $h out of range (1:12)")
    end
    -1 < mi < 60 || return ArgumentError("Minute: $mi out of range (0:59)")
    -1 < s < 60 || return ArgumentError("Second: $s out of range (0:59)")
    -1 < ms < 1000 || return ArgumentError("Millisecond: $ms out of range (0:999)")
    return nothing
end

DateTime(dt::Base.Libc.TmStruct) = DateTime(1900 + dt.year, 1 + dt.month, dt.mday, dt.hour, dt.min, dt.sec)

"""
    Date(y, [m, d]) -> Date

Construct a `Date` type by parts. Arguments must be convertible to [`Int64`](@ref).
"""
function Date(y::Int64, m::Int64=1, d::Int64=1)
    err = validargs(Date, y, m, d)
    err === nothing || throw(err)
    return Date(UTD(totaldays(y, m, d)))
end

function validargs(::Type{Date}, y::Int64, m::Int64, d::Int64)
    0 < m < 13 || return ArgumentError("Month: $m out of range (1:12)")
    0 < d < daysinmonth(y, m) + 1 || return ArgumentError("Day: $d out of range (1:$(daysinmonth(y, m)))")
    return nothing
end

Date(dt::Base.Libc.TmStruct) = Date(1900 + dt.year, 1 + dt.month, dt.mday)

"""
    Time(h, [mi, s, ms, us, ns]) -> Time

Construct a `Time` type by parts. Arguments must be convertible to [`Int64`](@ref).
"""
function Time(h::Int64, mi::Int64=0, s::Int64=0, ms::Int64=0, us::Int64=0, ns::Int64=0, ampm::AMPM=TWENTYFOURHOUR)
    err = validargs(Time, h, mi, s, ms, us, ns, ampm)
    err === nothing || throw(err)
    h = adjusthour(h, ampm)
    return Time(Nanosecond(ns + 1000us + 1000000ms + 1000000000s + 60000000000mi + 3600000000000h))
end

function validargs(::Type{Time}, h::Int64, mi::Int64, s::Int64, ms::Int64, us::Int64, ns::Int64, ampm::AMPM=TWENTYFOURHOUR)
    if ampm == TWENTYFOURHOUR # 24-hour clock
        -1 < h < 24 || return ArgumentError("Hour: $h out of range (0:23)")
    else
        0 < h < 13 || return ArgumentError("Hour: $h out of range (1:12)")
    end
    -1 < mi < 60 || return ArgumentError("Minute: $mi out of range (0:59)")
    -1 < s < 60 || return ArgumentError("Second: $s out of range (0:59)")
    -1 < ms < 1000 || return ArgumentError("Millisecond: $ms out of range (0:999)")
    -1 < us < 1000 || return ArgumentError("Microsecond: $us out of range (0:999)")
    -1 < ns < 1000 || return ArgumentError("Nanosecond: $ns out of range (0:999)")
    return nothing
end

Time(dt::Base.Libc.TmStruct) = Time(dt.hour, dt.min, dt.sec)

# Fallback constructors
DateTime(y, m=1, d=1, h=0, mi=0, s=0, ms=0, ampm::AMPM=TWENTYFOURHOUR) = DateTime(Int64(y), Int64(m), Int64(d), Int64(h), Int64(mi), Int64(s), Int64(ms), ampm)
Date(y, m=1, d=1) = Date(Int64(y), Int64(m), Int64(d))
Time(h, mi=0, s=0, ms=0, us=0, ns=0, ampm::AMPM=TWENTYFOURHOUR) = Time(Int64(h), Int64(mi), Int64(s), Int64(ms), Int64(us), Int64(ns), ampm)

