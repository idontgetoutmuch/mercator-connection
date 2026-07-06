import VersoBlog
import MercatorConnection

open Verso Genre Blog Site Syntax

def blog : Site := site MercatorConnection.FrontPage /
  "about"MercatorConnection.About
  "blog" MercatorConnection.Posts with
    MercatorConnection.Posts.FirstPost
    MercatorConnection.Posts.VersionStableLemmas
    MercatorConnection.Posts.MercatorVPost
    MercatorConnection.Posts.Mercatorintropost
    MercatorConnection.Posts.Mwepost

def main := blogMain .default blog
