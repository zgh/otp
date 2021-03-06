%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2008-2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%% This file is generated DO NOT EDIT

%% @doc See external documentation: <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html">wxAcceleratorEntry</a>.
%% @type wxAcceleratorEntry().  An object reference, The representation is internal
%% and can be changed without notice. It can't be used for comparsion
%% stored on disc or distributed for use on other nodes.

-module(wxAcceleratorEntry).
-include("wxe.hrl").
-export([destroy/1,getCommand/1,getFlags/1,getKeyCode/1,new/0,new/1,set/4,set/5]).

%% inherited exports
-export([parent_class/1]).

%% @hidden
parent_class(_Class) -> erlang:error({badtype, ?MODULE}).

%% @spec () -> wxAcceleratorEntry()
%% @equiv new([])
new() ->
  new([]).

%% @spec (X::term()|wxAcceleratorEntry()) -> wxAcceleratorEntry()
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html#wxacceleratorentrywxacceleratorentry">external documentation</a>.
%% <br /> Alternatives:
%% <p><c>
%% new([Option]) -> wxAcceleratorEntry() </c>
%%<br /> Option = {flags, integer()} | {keyCode, integer()} | {cmd, integer()} | {item, wxMenuItem:wxMenuItem()}
%% </p>
%% <p><c>
%% new(Entry::wxAcceleratorEntry()) -> wxAcceleratorEntry() </c>
%% </p>
new(Options)
 when is_list(Options) ->
  MOpts = fun({flags, Flags}, Acc) -> [<<1:32/?UI,Flags:32/?UI>>|Acc];
          ({keyCode, KeyCode}, Acc) -> [<<2:32/?UI,KeyCode:32/?UI>>|Acc];
          ({cmd, Cmd}, Acc) -> [<<3:32/?UI,Cmd:32/?UI>>|Acc];
          ({item, #wx_ref{type=ItemT,ref=ItemRef}}, Acc) ->   ?CLASS(ItemT,wxMenuItem),[<<4:32/?UI,ItemRef:32/?UI>>|Acc];
          (BadOpt, _) -> erlang:error({badoption, BadOpt}) end,
  BinOpt = list_to_binary(lists:foldl(MOpts, [<<0:32>>], Options)),
  wxe_util:construct(?wxAcceleratorEntry_new_1_0,
  <<BinOpt/binary>>);
new(#wx_ref{type=EntryT,ref=EntryRef}) ->
  ?CLASS(EntryT,wxAcceleratorEntry),
  wxe_util:construct(?wxAcceleratorEntry_new_1_1,
  <<EntryRef:32/?UI>>).

%% @spec (This::wxAcceleratorEntry()) -> integer()
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html#wxacceleratorentrygetcommand">external documentation</a>.
getCommand(#wx_ref{type=ThisT,ref=ThisRef}) ->
  ?CLASS(ThisT,wxAcceleratorEntry),
  wxe_util:call(?wxAcceleratorEntry_GetCommand,
  <<ThisRef:32/?UI>>).

%% @spec (This::wxAcceleratorEntry()) -> integer()
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html#wxacceleratorentrygetflags">external documentation</a>.
getFlags(#wx_ref{type=ThisT,ref=ThisRef}) ->
  ?CLASS(ThisT,wxAcceleratorEntry),
  wxe_util:call(?wxAcceleratorEntry_GetFlags,
  <<ThisRef:32/?UI>>).

%% @spec (This::wxAcceleratorEntry()) -> integer()
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html#wxacceleratorentrygetkeycode">external documentation</a>.
getKeyCode(#wx_ref{type=ThisT,ref=ThisRef}) ->
  ?CLASS(ThisT,wxAcceleratorEntry),
  wxe_util:call(?wxAcceleratorEntry_GetKeyCode,
  <<ThisRef:32/?UI>>).

%% @spec (This::wxAcceleratorEntry(), Flags::integer(), KeyCode::integer(), Cmd::integer()) -> ok
%% @equiv set(This,Flags,KeyCode,Cmd, [])
set(This,Flags,KeyCode,Cmd)
 when is_record(This, wx_ref),is_integer(Flags),is_integer(KeyCode),is_integer(Cmd) ->
  set(This,Flags,KeyCode,Cmd, []).

%% @spec (This::wxAcceleratorEntry(), Flags::integer(), KeyCode::integer(), Cmd::integer(), [Option]) -> ok
%% Option = {item, wxMenuItem:wxMenuItem()}
%% @doc See <a href="http://www.wxwidgets.org/manuals/stable/wx_wxacceleratorentry.html#wxacceleratorentryset">external documentation</a>.
set(#wx_ref{type=ThisT,ref=ThisRef},Flags,KeyCode,Cmd, Options)
 when is_integer(Flags),is_integer(KeyCode),is_integer(Cmd),is_list(Options) ->
  ?CLASS(ThisT,wxAcceleratorEntry),
  MOpts = fun({item, #wx_ref{type=ItemT,ref=ItemRef}}, Acc) ->   ?CLASS(ItemT,wxMenuItem),[<<1:32/?UI,ItemRef:32/?UI>>|Acc];
          (BadOpt, _) -> erlang:error({badoption, BadOpt}) end,
  BinOpt = list_to_binary(lists:foldl(MOpts, [<<0:32>>], Options)),
  wxe_util:cast(?wxAcceleratorEntry_Set,
  <<ThisRef:32/?UI,Flags:32/?UI,KeyCode:32/?UI,Cmd:32/?UI, BinOpt/binary>>).

%% @spec (This::wxAcceleratorEntry()) -> ok
%% @doc Destroys this object, do not use object again
destroy(Obj=#wx_ref{type=Type}) ->
  ?CLASS(Type,wxAcceleratorEntry),
  wxe_util:destroy(?wxAcceleratorEntry_destroy,Obj),
  ok.
