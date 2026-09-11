defmodule BobsBroadcastWeb.RadioLive do
  use BobsBroadcastWeb, :live_view

  alias BobsBroadcast.Radio.Broadcaster

  @impl true
  def mount(_params, _session, socket) do
    if connected?(socket) do
      Phoenix.PubSub.subscribe(BobsBroadcast.PubSub, "radio:now_playing")
    end

    listener_count = Registry.count(BobsBroadcast.Radio.ListenerRegistry)

    socket =
      socket
      |> assign(:now_playing, Broadcaster.now_playing())
      |> assign(:listener_count, listener_count)
      |> assign(:playing, Broadcaster.now_playing() != nil)

    {:ok, socket}
  end

  @impl true
  def handle_info({:now_playing, track_info}, socket) do
    {:noreply,
     socket
     |> assign(:now_playing, track_info)
     |> assign(:playing, track_info != nil)}
  end

  @impl true
  def handle_event("play", _params, socket) do
    Broadcaster.play()
    {:noreply, assign(socket, :playing, true)}
  end

  @impl true
  def handle_event("stop", _params, socket) do
    Broadcaster.stop_playback()
    {:noreply, assign(socket, :playing, false)}
  end

  @impl true
  def render(assigns) do
    ~H"""
    <div style="max-width: 500px; margin: 40px auto; font-family: monospace;">
      <h1>Bob's Broadcast</h1>

      <div style="background: #111; color: #0f0; padding: 20px; border-radius: 8px; margin-bottom: 20px;">
        <div :if={@now_playing} style="font-size: 18px; margin-bottom: 8px;">
          {@now_playing.title}
        </div>
        <div :if={!@now_playing} style="color: #666; font-style: italic;">
          Nothing playing
        </div>
      </div>

      <div style="margin-bottom: 20px;">
        <button :if={!@playing} phx-click="play" style="padding: 10px 20px; font-size: 16px;">
          Play
        </button>
        <button :if={@playing} phx-click="stop" style="padding: 10px 20px; font-size: 16px;">
          Stop
        </button>
      </div>

      <div style="margin-bottom: 20px;">
        <h3>Listen</h3>
        <audio id="radio-player" controls src="/radio/stream" style="width: 100%;"></audio>
      </div>

      <div style="color: #666; font-size: 12px;">
        Listeners: {@listener_count}
      </div>
    </div>
    """
  end
end
