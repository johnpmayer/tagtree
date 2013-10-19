
{-
    Copyright (c) John P Mayer Jr, 2013

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

module Data.TagTree where

import open Control.State

data TagTree leaf node edge 
  = Leaf leaf
  | Node node [(edge, TagTree leaf node edge)]

foldTagTree :
  (leaf -> a) ->
  (node -> [a] -> a) ->
  (edge -> a -> a) ->
  TagTree leaf node edge -> a
foldTagTree fLeaf fNode fEdge tree =
  let y = foldTagTree fLeaf fNode fEdge
      fChild (edge, child) = fEdge edge <| y child
  in case tree of
    Leaf leaf -> fLeaf leaf
    Node node subs -> fNode node <| map fChild subs

foldTagTree' :
  (leaf -> a) ->
  (node -> [(edge,a)] -> a) ->
  TagTree leaf node edge -> a
foldTagTree' fLeaf fNode tree =
  let y = foldTagTree' fLeaf fNode
  in case tree of
    Leaf leaf -> fLeaf leaf
    Node node subs -> 
      let mapAttach f (attach, s) = (attach, f s) 
          subs' = map (mapAttach y) subs
      in fNode node subs'

walkModify :
  (leaf -> State a leaf') ->
  (node -> State a node') ->
  (edge -> State a edge') ->
  TagTree leaf node edge ->
  State a (TagTree leaf' node' edge')
walkModify uLeaf uNode uEdge tree =
  let y = walkModify uLeaf uNode uEdge
      uSub (edge, sub) = 
        bindS (uEdge edge) (\edge' ->
        bindS (y sub) (\sub' ->
        returnS (edge', sub')))
  in case tree of
    Leaf leaf -> fmapS Leaf <| uLeaf leaf 
    Node node subs -> 
      bindS (mapMS uSub subs) (\subs' ->
      bindS (uNode node) (\node' ->
      returnS <| Node node' subs'))
