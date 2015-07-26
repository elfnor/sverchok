# ##### BEGIN GPL LICENSE BLOCK #####
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software Foundation,
#  Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
#
# ##### END GPL LICENSE BLOCK #####

''' by Eleanor Howick | 2015 https://github.com/elfnor
    LSystem code from Philip Rideout  https://github.com/prideout/lsystem '''


import string
import bpy
from bpy.props import BoolProperty, IntProperty, StringProperty

from sverchok.node_tree import SverchCustomTreeNode
from sverchok.data_structure import (changable_sockets, multi_socket,
                            SvSetSocketAnyType, SvGetSocketAnyType, updateNode,
                            fullList, Vector_generate, Matrix_listing)

import random
import mathutils as mu
import logging

import xml.etree.cElementTree as etree
from xml.etree.cElementTree import fromstring

import itertools

def flat(*args):
    for x in args:
        if hasattr(x, '__iter__'):
            for y in flat(*x):
                yield y
        else:
            yield x

fixed_item = [0, 1, 1, 1, 0, 0, 0, 0]
iterfi = 0

"""
---------------------------------------------------
    LSystem
---------------------------------------------------
"""


class LSystem:
    """
    Takes an XML string.
    """
    def __init__(self, rules, maxObjects):
        self._tree = fromstring(rules)
        self._maxDepth = int(self._tree.get("max_depth"))
        self._voxelSize = self._tree.get("clearance")
        logging.basicConfig(level=logging.INFO,
             format='%(levelname)-8s %(filename)s:%(lineno)-4d: %(message)s')
        logging.info("clearance %s" % (self._voxelSize))

        self._progressCount = 0
        self._maxObjects = maxObjects
        self.matrix = mu.Matrix.Identity(4)
        self.locs = set()
        

    """
    Returns a list of "shapes".
    Each shape is a 2-tuple: (shape name, transform matrix).
    """

    def _process_rule(self):
        for statement in self.rule:              
            tstr = statement.get("transforms","")
            if not(tstr):
                tstr = ''
                for t in ['tx', 'ty', 'tz', 'rx', 'ry', 'rz', 'sa', 'sx', 'sy', 'sz']:
                    tvalue = statement.get(t)
                    if tvalue:
                        n = eval(tvalue)
                        tstr += "{} {:f} ".format(t,n) 
            xform = _parseXform(tstr)
            count = int(statement.get("count", 1))
            for n in range(count):
                self.matrix *= xform
                
                if statement.tag == "call":
                    self.rule = _pickRule(self._tree, statement.get("rule"))
                    cloned_matrix = self.matrix.copy()
                    entry = (self.rule, self.depth + 1, cloned_matrix)     
                    self.stack.append(entry)
              
                elif statement.tag == "instance":
                    vecTrans = self.matrix.to_translation()
                    if self._voxelSize:
                        loc_key = tuple(
                                    [round(i)
                                    for i
                                    in vecTrans / float(self._voxelSize)])
                    else:
                        loc_key = (0, 0, 0)
                    if loc_key in self.locs:
                        logging.info('{0} voxel_stop {1} {2}'.format(loc_key, tstr, vecTrans))
                        return # to while loop
                    else:                        
                        if self._voxelSize:
                            self.locs.add(loc_key) 
                        name = statement.get("shape")
                        shape = (name, self.matrix)
                        self.shapes.append(shape)
                else:
                    raise ValueError("bad xml", statement.tag)
        return

    def evaluate(self, seed=0):
        random.seed(seed)
        self.rule = _pickRule(self._tree, "entry")
        entry = (self.rule, 0, mu.Matrix.Identity(4))
        self.shapes = self._evaluate(entry)
        return self.shapes

    def _evaluate(self, entry):
        self.stack = [entry]
        self.shapes = []
        locs = set()
        voxel_stop = False
        last_loc_key = None
        while len(self.stack) > 0:

            if len(self.shapes) > self._maxObjects:
                print(('max objects reached', len(self.shapes), self._maxObjects))
                break # out of while len(stack) > 0: loop

            if len(self.shapes) > self._progressCount + 1000:
                print((len(self.shapes), "curve segments so far"))
                print((self._maxObjects))
                self._progressCount = len(self.shapes)

            self.rule, self.depth, self.matrix = self.stack.pop()

            local_max_depth = self._maxDepth
            if "max_depth" in self.rule.attrib:
                local_max_depth = int(self.rule.get("max_depth"))

            if len(self.stack) >= self._maxDepth:
                self.shapes.append(None)
                logging.info('shape len(stack) >= self._maxDepth None')
                continue # with next iteration of while len(stack) > 0: loop

            if self.depth >= local_max_depth:
                if "successor" in self.rule.attrib:
                    successor = self.rule.get("successor")
                    self.rule = _pickRule(self._tree, successor)
                    self.stack.append((self.rule, 0, self.matrix))
                self.shapes.append(None)
                logging.info('shape depth >= local_max_depth None')
                continue  # with next iteration of while len(stack) > 0: loop
            
            self._process_rule()

        print(("\nGenerated %d shapes." % len(self.shapes)))
        return self.shapes
        # end of _evaluate

    def make_tube(self, mats, verts):
        """
        takes a list of vertices and a list of matrices
        the vertices are to be joined in a ring,
        copied and transformed by the 1st matrix
        and this ring joined to the previous ring.

        The ring dosen't have to be planar.
        outputs lists of vertices, edges and faces
        """

        edges_out = []
        verts_out = []
        faces_out = []
        vID = 0
        if len(mats) > 1:
            #print('len mats', len(mats))
            #print(mats[0])
            nring = len(verts[0])
            #end face
            faces_out.append(list(range(nring)))
            for i, m in enumerate(mats):
                for j, v in enumerate(verts[0]):
                    vout = mu.Matrix(m) * mu.Vector(v)
                    verts_out.append(vout.to_tuple())
                    vID = j + i * nring
                    #rings
                    if j != 0:
                        edges_out.append([vID, vID - 1])
                    else:
                        edges_out.append([vID, vID + nring - 1])
                    #lines
                    if i != 0:
                        edges_out.append([vID, vID - nring])
                        #faces
                        if j != 0:
                            faces_out.append([vID,
                                              vID - nring,
                                              vID - nring - 1,
                                              vID - 1])
                        else:
                            faces_out.append([vID,
                                              vID - nring,
                                              vID - 1,
                                              vID + nring - 1])
            #end face
            #reversing list fixes face normal direction keeps mesh manifold
            f = list(range(vID, vID - nring, - 1))
            faces_out.append(f)
        return verts_out, edges_out, faces_out



def _pickRule(tree, name):
    rules = tree.findall("rule")
    elements = []
    for r in rules:
        if r.get("name") == name:
            elements.append(r)

    if len(elements) == 0:
        raise ValueError("bad xml", "no rules found with name '%s'" % name)

    sum, tuples = 0, []
    for e in elements:
        weight = int(e.get("weight", 1))
        sum = sum + weight
        tuples.append((e, weight))
    n = random.randint(0, sum - 1)
    for (item, weight) in tuples:
        if n < weight:
            break
        n = n - weight
    return item

_xformCache = {}


def _parseXform(xform_string):
    if xform_string in _xformCache:
        return _xformCache[xform_string]

    matrix = mu.Matrix.Identity(4)
    tokens = xform_string.split(' ')
    t = 0
    while t < len(tokens) - 1:
            command, t = tokens[t], t + 1

            # Translation
            if command == 'tx':
                x, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Translation(mu.Vector((x, 0, 0)))
            elif command == 'ty':
                y, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Translation(mu.Vector((0, y, 0)))
            elif command == 'tz':
                z, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Translation(mu.Vector((0, 0, z)))
            elif command == 't':
                x, t = eval(tokens[t]), t + 1
                y, t = eval(tokens[t]), t + 1
                z, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Translation(mu.Vector((x, y, z)))

            # Rotation
            elif command == 'rx':
                theta, t = _radians(eval(tokens[t])), t + 1
                matrix *= mu.Matrix.Rotation(theta, 4, 'X')

            elif command == 'ry':
                theta, t = _radians(eval(tokens[t])), t + 1
                matrix *= mu.Matrix.Rotation(theta, 4, 'Y')
            elif command == 'rz':
                theta, t = _radians(eval(tokens[t])), t + 1
                matrix *= mu.Matrix.Rotation(theta, 4, 'Z')

            # Scale
            elif command == 'sx':
                x, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Scale(x, 4, mu.Vector((1.0, 0.0, 0.0)))
            elif command == 'sy':
                y, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Scale(y, 4, mu.Vector((0.0, 1.0, 0.0)))
            elif command == 'sz':
                z, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Scale(z, 4, mu.Vector((0.0, 0.0, 1.0)))
            elif command == 'sa':
                v, t = eval(tokens[t]), t + 1
                matrix *= mu.Matrix.Scale(v, 4)
            elif command == 's':
                x, t = eval(tokens[t]), t + 1
                y, t = eval(tokens[t]), t + 1
                z, t = eval(tokens[t]), t + 1
                mx = mu.Matrix.Scale(x, 4, mu.Vector((1.0, 0.0, 0.0)))
                my = mu.Matrix.Scale(y, 4, mu.Vector((0.0, 1.0, 0.0)))
                mz = mu.Matrix.Scale(z, 4, mu.Vector((0.0, 0.0, 1.0)))
                mxyz = mx * my * mz
                matrix *= mxyz

            else:
                raise ValueError("bad xml", "unrecognized transformation: '%s' at position %d in '%s'" % (command, t, xform_string))

    _xformCache[xform_string] = matrix
    return matrix


def _radians(d):
    return float(d * 3.141 / 180.0)

"""
---------------------------------------------------
    SvGenerativeArtNode
---------------------------------------------------
"""


class SvGenerativeArtNode(bpy.types.Node, SverchCustomTreeNode):
    ''' Generative Art or LSystem node'''
    bl_idname = 'SvGenerativeArtNode'
    bl_label = 'Generative Art'
    bl_icon = 'OUTLINER_OB_EMPTY'

    filename = StringProperty(default="", update=updateNode)

    rseed = IntProperty(name='rseed', description='random seed',
                       default=21, min=0, options={'ANIMATABLE'},
                       update=updateNode)

    maxmats = IntProperty(name='maxmats',
                       description='maximum nunber of matrices',
                       default=1000, min=1, options={'ANIMATABLE'},
                       update=updateNode)

    typ = StringProperty(name='typ',
                         default='')
    newsock = BoolProperty(name='newsock',
                           default=False)

    base_name = 'data '
    multi_socket_type = 'StringsSocket'

    def draw_buttons(self, context, layout):
        layout.prop_search(self, 'filename', bpy.data,
                          'texts', text='', icon='TEXT')
        layout.prop(self, "rseed", text="r seed")
        layout.prop(self, "maxmats", text="max mats")

    def sv_init(self, context):
        self.inputs.new('VerticesSocket', "Vertices")
        self.inputs.new('StringsSocket', "data", "data")

        self.outputs.new('MatrixSocket', "Matrices")
        self.outputs.new('StringsSocket', "Mask")

        self.outputs.new('VerticesSocket', "Vertices")
        self.outputs.new('StringsSocket', "Edges")
        self.outputs.new('StringsSocket', "Faces")

    def update(self):
        # inputs
        multi_socket(self, min=2)

        if 'data' in self.inputs and self.inputs['data'].links:
            # adaptive socket
            inputsocketname = 'data'
            outputsocketname = ['data']
            changable_sockets(self, inputsocketname, outputsocketname)

    def process(self):
        if not self.filename:
            return
        #xml text must be an internal file
        if not (self.filename in bpy.data.texts):
            return
        internal_file = bpy.data.texts[self.filename]
        self.xml_text = internal_file.as_string()
        #nvars may be too large because of repeats
        nvars = self.xml_text.count('{')

        if ((self.outputs['Matrices'].is_linked) or (self.outputs['Vertices'].is_linked)):
            slots = []
            for socket in self.inputs[1:]:
                if socket.is_linked:
                    slots.append(SvGetSocketAnyType(self, socket))
            #flatten vars
            if slots:
                slots = list(flat(slots))
                fullList(slots, nvars)
            else:
                slots = [0] * nvars

            self.xml_text = self.xml_text.format(*slots)

            lsys = LSystem(self.xml_text, self.maxmats)
            shapes = lsys.evaluate(seed=self.rseed)

            names = [shape[0] for shape in shapes if shape]
            #convert names to integer list
            iddict = {k: v for v, k in enumerate(sorted(set(names)))}

            mat_sublist = []
            mat_list = []
            mask_list = []

            edges_out = []
            verts_out = []
            faces_out = []
            #make last entry in shapes None
            #to allow make tube to finish last tube
            if shapes[-1]:
                shapes.append(None)
            for i, shape in enumerate(shapes):
                if shape:
                    mat_sublist.append(shape[1])
                    mat_list.append(shape[1])
                    mask_list.append(iddict[shape[0]])
                else:
                    if len(mat_sublist) > 0:
                        if self.inputs['Vertices'].is_linked:
                            verts = Vector_generate(SvGetSocketAnyType(self, self.inputs['Vertices']))
                            v, e, f = lsys.make_tube(mat_sublist, verts)
                            if v:
                                verts_out.append(v)
                                edges_out.append(e)
                                faces_out.append(f)

                    mat_sublist = []

            if self.outputs['Matrices'].is_linked:
                SvSetSocketAnyType(self, 'Matrices', Matrix_listing(mat_list))
            if self.outputs['Mask'].is_linked:
                SvSetSocketAnyType(self, 'Mask', [mask_list])

            if self.outputs['Vertices'].is_linked:
                SvSetSocketAnyType(self, 'Vertices', verts_out)
            if self.outputs['Edges'].is_linked:
                SvSetSocketAnyType(self, 'Edges', edges_out)
            if self.outputs['Faces'].is_linked:
                SvSetSocketAnyType(self, 'Faces', faces_out)

    def update_socket(self, context):
        self.update()


def register():
    bpy.utils.register_class(SvGenerativeArtNode)


def unregister():
    bpy.utils.unregister_class(SvGenerativeArtNode)

if __name__ == '__main__':
    register()


