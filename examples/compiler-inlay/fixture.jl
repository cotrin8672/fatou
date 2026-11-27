function scaled(x::T) where {T<:Real}
    y = x * 2
    return y + one(x)
end
function branch(flag::Bool)
    return flag ? 1 : missing
end
function configured(x; factor=2)
    return x * factor
end
function callers()
    a = scaled(2)
    β = scaled(2.0)
    c = branch(true)
    d = configured(2; factor=2.5)
    return a, β, c, d
end
function any_input(values::Vector{Any})
    item = values[1]
    return item
end

function no_normal_return()
    throw(ArgumentError("fixture not called during inference"))
end

function maybe_none(flag::Bool)
    return flag ? 7 : nothing
end
