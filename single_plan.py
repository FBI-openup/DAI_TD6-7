""" Find a path for the robot
"""

from math import floor, ceil
import argparse
from tkinter import Tk, Canvas, LAST
import os
import sys
import json
from fractions import Fraction
import functools

from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    is_valid,
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff, Equals,
    GE, GT, LT, LE
)
from pysmt.logics import QF_LRA

class Map():
    def __init__(self, map_file = None):
        # Bounds of the map
        # The numbers are represented as a Real objects from PySMT
        # Real represents a rational number.
        self.min_x = Real(0)
        self.min_y = Real(0)
        self.max_x = Real(0)
        self.max_y = Real(0)

        # Coordinates of the initial point
        self.x0 = Real(0)
        self.y0 = Real(0)

        # Coordinates of the target point
        self.xf = Real(0)
        self.yf = Real(0)

        # List of obstacles
        #
        # An obstacle is a list of 4 real numbers identifying
        # the coordinate of the lower_x, upper_x, lower_y, upper_y
        #
        # If you take an element obstacle of self.obstacles, you can get the
        # coordinate of the rectangle as:
        # (lower_x, upper_x, lower_y, upper_y) = obstacle
        self.obstacles = []

        # Initialize the map from a file
        if (not map_file is None):
            self._read_map(map_file)

    def _read_map(self, input_map):
        def read_rational(json_data):
            assert len(json_data) == 2
            return Real(Fraction(json_data[0], json_data[1]))

        data = []
        with open(input_map) as f:
            data = json.load(f)

            # all the fields in the file
            assert functools.reduce(lambda res, elem : res and elem in data, ["init","target","obstacles","bounds"], True)

            assert len(data["bounds"]) == 4
            self.min_x = read_rational(data["bounds"][0])
            self.max_x = read_rational(data["bounds"][1])
            self.min_y = read_rational(data["bounds"][2])
            self.max_y = read_rational(data["bounds"][3])

            assert len(data["init"]) == 2
            assert len(data["init"][0]) == 2 and len(data["init"][1]) == 2
            self.x0 = read_rational(data["init"][0])
            self.y0 = read_rational(data["init"][1])

            assert len(data["target"]) == 2
            assert len(data["target"][0]) == 2 and len(data["target"][1]) == 2
            self.xf = read_rational(data["target"][0])
            self.yf = read_rational(data["target"][1])

            for obstacle in data["obstacles"]:
                assert len(obstacle) == 4
                obs = (read_rational(obstacle[0]),
                       read_rational(obstacle[1]),
                       read_rational(obstacle[2]),
                       read_rational(obstacle[3]))
                self.obstacles.append(obs)

def draw(map_1, trace):
    top = Tk()

    has_trace = len(trace) > 0

    if (not has_trace):
        trace = [
            (Fraction(map_1.x0.serialize()),
             Fraction(map_1.y0.serialize())),
            (Fraction(map_1.xf.serialize()),
             Fraction(map_1.yf.serialize()))]

    def to_float(f):
        if f.denominator == 0:
            return 0
        else:
            return float(f.numerator) / float(f.denominator)

    canvas_width = 500
    canvas_height = 500

    min_x = functools.reduce(lambda res, elem : res if res <= to_float(elem[0]) else to_float(elem[0]), trace, -6)
    max_x = functools.reduce(lambda res, elem : res if res >= to_float(elem[0]) else to_float(elem[0]), trace, 6)
    min_y = functools.reduce(lambda res, elem : res if res <= to_float(elem[1]) else to_float(elem[1]), trace, -6)
    max_y = functools.reduce(lambda res, elem : res if res >= to_float(elem[1]) else to_float(elem[1]), trace, 6)

    def point_in_canvas(x,y):
        def point_in_canvas_aux(x,min_x,max_x,canvas_width):
            return ( (x - min_x) / (max_x - min_x) ) * canvas_width

        bound = 10
        canvas_width_visible = canvas_width - 2*bound
        canvas_height_visible = canvas_height - 2*bound

        return (float(bound + point_in_canvas_aux(x, min_x, max_x, canvas_width_visible)),
                float(bound + canvas_height_visible - point_in_canvas_aux(y, min_y, max_y, canvas_height_visible)))

    # Code to add widgets will go here...

    w = Canvas(top,
               width=canvas_width,
               height=canvas_height)

    # Print the axes
    (min_x_canvas, min_y_canvas) = point_in_canvas(min_x,min_y)
    (max_x_canvas, max_y_canvas) = point_in_canvas(max_x,max_y)
    (canvas_origin_x, canvas_origin_y) = point_in_canvas(0,0)
    w.create_line(min_x_canvas, canvas_origin_y , max_x_canvas, canvas_origin_y,dash=(4,2))
    w.create_line(canvas_origin_x, min_y_canvas, canvas_origin_x , max_y_canvas,dash=(4,2))

    for x in range(floor(min_x), ceil(max_x)):
        (x_canvas, _) = point_in_canvas(x, 0)
        w.create_text(x_canvas,canvas_origin_y + 10,fill="black",
                      text="%s" % str(x))

    for y in range(floor(min_y), ceil(max_y)):
        (_, y_canvas) = point_in_canvas(0, y)
        w.create_text(canvas_origin_x - 10,y_canvas, fill="black",
                      text="%s" % str(y))

    # Print the obstacles
    for obs in map_1.obstacles:
        x_lower, x_upper, y_lower, y_upper = obs
        (x_lower_canvas, y_lower_canvas) = point_in_canvas(to_float(Fraction(str(x_lower))),
                                                           to_float(Fraction(str(y_lower))))
        (x_upper_canvas, y_upper_canvas) = point_in_canvas(to_float(Fraction(str(x_upper))),
                                                           to_float(Fraction(str(y_upper))))

        assert (x_lower_canvas <= x_upper_canvas)
        assert (y_lower_canvas >= y_upper_canvas)


        w.create_rectangle(x_lower_canvas,
                           y_upper_canvas,
                           x_upper_canvas,
                           y_lower_canvas,
                           outline='red',
                           fill="blue")



    # Print the trace
    px,py = None, None
    for (x,y) in trace:
        (x_canvas, y_canvas) = point_in_canvas(to_float(x),to_float(y))

        radius = 5
        w.create_oval(x_canvas - radius,
                      y_canvas + radius,
                      x_canvas + radius,
                      y_canvas - radius,
                      fill='red')

        if (has_trace and not px is None):
            w.create_line(px, py, x_canvas, y_canvas, arrow=LAST)

        px, py = x_canvas,y_canvas


    w.pack()
    w.update()
    # w.postscript(file="plan.eps")

    top.mainloop()

def get_encoding(map_1, k):
    """
    Retuns the encoding of a robot path taking k action
    """
    formulas = []

    x = []
    y = []
    actions = []  

    for i in range(k + 1):
        x_i = Symbol(f"x_{i}", REAL)
        y_i = Symbol(f"y_{i}", REAL)
        x.append(x_i)
        y.append(y_i)

    for i in range(k):
        l_i = Symbol(f"l_{i}", BOOL)
        r_i = Symbol(f"r_{i}", BOOL)
        u_i = Symbol(f"u_{i}", BOOL)
        d_i = Symbol(f"d_{i}", BOOL)
        actions.append({"l": l_i, "r": r_i, "u": u_i, "d": d_i})

    formulas.append(Equals(x[0], map_1.x0))
    formulas.append(Equals(y[0], map_1.y0))

    formulas.append(Equals(x[k], map_1.xf))
    formulas.append(Equals(y[k], map_1.yf))

    for i in range(k):
        curr_x, curr_y = x[i], y[i]
        next_x, next_y = x[i+1], y[i+1]
        
        l, r, u, d = actions[i]["l"], actions[i]["r"], actions[i]["u"], actions[i]["d"]

        formulas.append(Or(l, r, u, d))
        formulas.append(Not(And(l, r)))
        formulas.append(Not(And(l, u)))
        formulas.append(Not(And(l, d)))
        formulas.append(Not(And(r, u)))
        formulas.append(Not(And(r, d)))
        formulas.append(Not(And(u, d)))

        formulas.append(Implies(l, And(Equals(next_x, curr_x - Real(1)), Equals(next_y, curr_y))))
        formulas.append(Implies(r, And(Equals(next_x, curr_x + Real(1)), Equals(next_y, curr_y))))
        formulas.append(Implies(u, And(Equals(next_x, curr_x), Equals(next_y, curr_y + Real(1)))))
        formulas.append(Implies(d, And(Equals(next_x, curr_x), Equals(next_y, curr_y - Real(1)))))

        formulas.append(GE(curr_x, map_1.min_x))
        formulas.append(LE(curr_x, map_1.max_x))
        formulas.append(GE(curr_y, map_1.min_y))
        formulas.append(LE(curr_y, map_1.max_y))

        for obs in map_1.obstacles:
            x_min, x_max, y_min, y_max = obs
            formulas.append(Or(
                LT(curr_x, Real(Fraction(str(x_min)))),
                GT(curr_x, Real(Fraction(str(x_max)))),
                LT(curr_y, Real(Fraction(str(y_min)))),
                GT(curr_y, Real(Fraction(str(y_max))))
            ))

    formulas.append(GE(x[k], map_1.min_x))
    formulas.append(LE(x[k], map_1.max_x))
    formulas.append(GE(y[k], map_1.min_y))
    formulas.append(LE(y[k], map_1.max_y))
    for obs in map_1.obstacles:
        x_min, x_max, y_min, y_max = obs
        formulas.append(Or(
            LT(x[k], Real(Fraction(str(x_min)))),
            GT(x[k], Real(Fraction(str(x_max)))),
            LT(y[k], Real(Fraction(str(y_min)))),
            GT(y[k], Real(Fraction(str(y_max))))
        ))

    return And(formulas)

def find_trace(encoding, k):
    """ Return the list of points where the robot changed its direction.

    We represent a point as a pair, the x and y coordinate of the point,
    and each coordinate is a Fraction object (from the fractions package)

    You can use the function get_fraction_from_value to get a fraction
    from a value obtained with the solver.get_value function.
    """
    def get_fraction_from_value(value):
        return Fraction(value.serialize())

    solver = Solver(name="z3")
    solver.add_assertion(encoding)

    if not solver.solve():
        return []

    trace = []
    for i in range(k + 1):
        x_node = Symbol(f"x_{i}", REAL)
        y_node = Symbol(f"y_{i}", REAL)
        
        x_val = solver.get_value(x_node)
        y_val = solver.get_value(y_node)
        
        trace.append((get_fraction_from_value(x_val), get_fraction_from_value(y_val)))

    return trace


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--map")
    parser.add_argument("--k",  default=1, type=int)
    args = parser.parse_args()

    input_map = args.map
    map_1 = Map(input_map)

    # Find a solution with exactly k steps
    k = args.k

    # Get the encoding
    encoding = get_encoding(map_1, k)

    # solve the encoding
    trace = find_trace(encoding, k)

    if (len(trace) > 0):
        # Draw the solution
        draw(map_1, trace)
    else:
        print("Did not find a path of %d length" % k)
        draw(map_1, [])



if __name__ == '__main__':
    main()



